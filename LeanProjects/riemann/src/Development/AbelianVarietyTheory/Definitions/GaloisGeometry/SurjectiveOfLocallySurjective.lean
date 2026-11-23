import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CoeEqAlgebraMapZeroEquiv
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange

set_option autoImplicit false

open TensorProduct

noncomputable section
namespace GlobalTheory.HodgeCoh
open GlobalTheory.CechDR

section ProjTrace

variable (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] [Module.Finite R M]
  [Module.Projective R M]

def projTrace : Module.End R M →ₗ[R] R :=
  contractLeft R M ∘ₗ (dualTensorHomEquiv R M M).symm.toLinearMap

variable {R M}

theorem projTrace_dualTensorHom (t : Module.Dual R M ⊗[R] M) :
    projTrace R M (dualTensorHom R M M t) = contractLeft R M t :=
  congrArg (contractLeft R M) ((dualTensorHomEquiv R M M).symm_apply_apply t)

theorem projTrace_smulRight (ξ : Module.Dual R M) (m : M) :
    projTrace R M (ξ.smulRight m) = ξ m := by
  have : ξ.smulRight m = dualTensorHom R M M (ξ ⊗ₜ m) := by ext; simp
  rw [this, projTrace_dualTensorHom, contractLeft_apply]

theorem projTrace_eq_trace [Module.Free R M] (φ : Module.End R M) :
    projTrace R M φ = LinearMap.trace R M φ := by
  obtain ⟨t, rfl⟩ := (dualTensorHom_bijective (R := R) (M := M) (N := M)).2 φ
  rw [projTrace_dualTensorHom, LinearMap.trace_eq_contract_apply]

theorem projTrace_of_isBaseChange {S N : Type*} [CommRing S] [Algebra R S] [AddCommGroup N]
    [Module R N] [Module S N] [IsScalarTower R S N] [Module.Finite S N] [Module.Projective S N]
    {l : M →ₗ[R] N} (hl : IsBaseChange S l) (φ : Module.End R M) (ψ : Module.End S N)
    (h : ∀ x, ψ (l x) = l (φ x)) : projTrace S N ψ = algebraMap R S (projTrace R M φ) := by
  have key : ∀ t : Module.Dual R M ⊗[R] M, ∃ t' : Module.Dual S N ⊗[S] N,
      (∀ x, dualTensorHom S N N t' (l x) = l (dualTensorHom R M M t x)) ∧
        contractLeft S N t' = algebraMap R S (contractLeft R M t) := fun t ↦ by
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp, by simp⟩
    | add a b ha hb =>
      obtain ⟨a', h1, h2⟩ := ha
      obtain ⟨b', h3, h4⟩ := hb
      exact ⟨a' + b', fun x ↦ by simp [h1, h3], by simp [h2, h4]⟩
    | tmul ξ m =>
      refine ⟨hl.lift (Algebra.linearMap R S ∘ₗ ξ) ⊗ₜ l m, fun x ↦ ?_, ?_⟩
      · simp [hl.lift_eq]
      · simp [hl.lift_eq]
  obtain ⟨t, rfl⟩ := (dualTensorHom_bijective (R := R) (M := M) (N := M)).2 φ
  obtain ⟨t', h1, h2⟩ := key t
  have : ψ = dualTensorHom S N N t' := hl.algHom_ext _ _ fun x ↦ (h x).trans (h1 x).symm
  rw [this, projTrace_dualTensorHom, projTrace_dualTensorHom, h2]

theorem projTrace_id_of_rankAtStalk {d : ℕ} (h : ∀ p, Module.rankAtStalk (R := R) M p = d) :
    projTrace R M LinearMap.id = d := by
  refine Module.eq_of_localization_maximal (fun P _ ↦ Localization.AtPrime P)
    (fun P _ ↦ Algebra.linearMap R (Localization.AtPrime P)) _ _ fun P hP ↦ ?_
  rw [Algebra.linearMap_apply, Algebra.linearMap_apply]
  have hb := IsLocalizedModule.isBaseChange P.primeCompl (Localization.AtPrime P)
    (LocalizedModule.mkLinearMap P.primeCompl M)
  have : Module.Free (Localization.AtPrime P) (LocalizedModule P.primeCompl M) :=
    Module.free_of_flat_of_isLocalRing
  rw [← projTrace_of_isBaseChange hb LinearMap.id LinearMap.id (fun _ ↦ rfl), projTrace_eq_trace,
    LinearMap.trace_id, map_natCast, ← h ⟨P, hP.isPrime⟩]
  rfl

end ProjTrace

section AlgTrace

variable (B B' : Type*) [CommRing B] [CommRing B'] [Algebra B B'] [Module.Finite B B']
  [Module.Projective B B']

def algTrace : B' →ₗ[B] B := projTrace B B' ∘ₗ LinearMap.mul B B'

variable {B B'}

theorem algTrace_apply (b : B') : algTrace B B' b = projTrace B B' (LinearMap.mul B B' b) := rfl

theorem algTrace_eq_trace [Module.Free B B'] (b : B') : algTrace B B' b = Algebra.trace B B' b :=
  projTrace_eq_trace _

theorem algTrace_of_isPushout {C C' : Type*} [CommRing C] [CommRing C'] [Algebra B C]
    [Algebra C C'] [Algebra B' C'] [Algebra B C'] [IsScalarTower B C C'] [IsScalarTower B B' C']
    [Module.Finite C C'] [Module.Projective C C'] [h : Algebra.IsPushout B C B' C'] (b : B') :
    algTrace C C' (algebraMap B' C' b) = algebraMap B C (algTrace B B' b) :=
  projTrace_of_isBaseChange h.out _ _ fun x ↦ (map_mul (algebraMap B' C') b x).symm

theorem algTrace_one {d : ℕ} (h : ∀ p, Module.rankAtStalk (R := B) B' p = d) :
    algTrace B B' 1 = d := by
  rw [algTrace_apply, ← projTrace_id_of_rankAtStalk h]
  congr 1
  ext; simp

theorem algTrace_algebraMap_of_bijective (h : Function.Bijective (algebraMap B B')) (b : B) :
    algTrace B B' (algebraMap B B' b) = b := by
  let e := LinearEquiv.ofBijective (Algebra.linearMap B B') h
  have : Module.Free B B' := .of_equiv e
  rw [algTrace_eq_trace, ← Algebra.trace_eq_of_algEquiv (AlgEquiv.ofBijective (Algebra.ofId B B') h).symm]
  simp

end AlgTrace

section Forms

variable (k B B' : Type) [CommRing k] [CommRing B] [CommRing B'] [Algebra k B] [Algebra k B']
  [Algebra B B'] [IsScalarTower k B B']

theorem semiHom_algebraMap : SemiHom (RingHom.id k) (algebraMap B B') := fun r b ↦ by
  rw [RingHom.id_apply, Algebra.smul_def, Algebra.smul_def, map_mul,
    ← IsScalarTower.algebraMap_apply]

def formLin (j : ℕ) : Om k B j →ₗ[B] Om k B' j where
  toFun := (semiHom_algebraMap k B B').mOm j
  map_add' := map_add _
  map_smul' b x := by
    rw [SemiHom.mOm_smul, RingHom.id_apply, algebraMap_smul]

theorem formLin_apply {j : ℕ} (x : Om k B j) :
    formLin k B B' j x = (semiHom_algebraMap k B B').mOm j x := rfl

theorem isBaseChange_formLin [Algebra.FormallyEtale B B'] (j : ℕ) :
    IsBaseChange B' (formLin k B B' j) := by
  convert GlobalTheory.TopForm.isBaseChange_exteriorPower
    (KaehlerDifferential.isBaseChange_of_formallyEtale k B B') j
  apply exteriorPower.linearMap_ext
  ext1 v
  simp only [LinearMap.compAlternatingMap_apply, exteriorPowerMapOver_ιMulti]
  refine Subtype.ext ?_
  change (semiHom_algebraMap k B B').mDR (exteriorPower.ιMulti B j v : DR k B) = _
  rw [exteriorPower.ιMulti_apply_coe, exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_apply,
    ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn]
  congr 2
  funext i
  exact (SemiHom.mDR_ι _ _).trans (congrArg ι1 (SemiHom.oneFormMap_eq_kaehlerDifferential_map _ (fun _ ↦ rfl) _))

theorem projective_of_etale [Module.Finite B B'] [Algebra.Etale B B'] : Module.Projective B B' :=
  have : Module.FinitePresentation B B' := .of_finite_of_finitePresentation B B'
  Module.Flat.projective_of_finitePresentation

variable [Module.Finite B B'] [Algebra.Etale B B']

def etTrace : B' →ₗ[B] B := have := projective_of_etale B B'; algTrace B B'

def formTrace (j : ℕ) : Om k B' j →ₗ[B] Om k B j :=
  (TensorProduct.lid B (Om k B j)).toLinearMap ∘ₗ (etTrace B B').rTensor (Om k B j) ∘ₗ
    ((isBaseChange_formLin k B B' j).equiv.symm.toLinearMap.restrictScalars B)

theorem formTrace_smul_formLin {j : ℕ} (b : B') (x : Om k B j) :
    formTrace k B B' j (b • formLin k B B' j x) = etTrace B B' b • x := by
  have := (isBaseChange_formLin k B B' j).equiv_tmul b x
  simp only [formTrace, LinearMap.comp_apply, LinearMap.restrictScalars_apply, LinearEquiv.coe_coe,
    ← this, LinearEquiv.symm_apply_apply, LinearMap.rTensor_tmul, TensorProduct.lid_tmul]

end Forms

section Glue

theorem surjective_of_locally_surjective {A M N : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (θ : M →ₗ[A] N) (Z : A → Submodule A N)
    (h1 : ∀ g h, Z g ≤ Z (g * h)) (h2 : ∀ g (m : ℕ) n, g ^ m • n ∈ Z g → n ∈ Z g)
    (h3 : ∀ t : Set A, Ideal.span t = ⊤ → ∀ n, (∀ g ∈ t, n ∈ Z g) → n = 0)
    (h4 : ∀ g y, θ y ∈ Z g → ∃ m : ℕ, g ^ m • y = 0)
    (h5 : ∀ n, Ideal.span {g | ∃ (m : ℕ) (y : M), g ^ m • n - θ y ∈ Z g} = ⊤) :
    Function.Surjective θ := fun n ↦ by
  obtain ⟨t, ht, ht'⟩ := (Ideal.span_eq_top_iff_finite _).1 (h5 n)
  refine Submodule.mem_of_span_eq_top_of_smul_pow_mem (LinearMap.range θ) _ (h5 n) n ?_
  rintro ⟨g, m, y, hy⟩
  have key : ∀ i : t, ∃ r : ℕ, g ^ r • (g ^ m • n - θ y) ∈ Z i := fun ⟨i, hi⟩ ↦ by
    obtain ⟨m', y', hy'⟩ := ht hi
    have e : θ (g ^ m • y' - i ^ m' • y) =
        i ^ m' • (g ^ m • n - θ y) - g ^ m • (i ^ m' • n - θ y') := by
      simp only [map_sub, map_smul, smul_sub, smul_comm (i ^ m') (g ^ m)]; abel
    obtain ⟨r, hr⟩ := h4 (i * g) (g ^ m • y' - i ^ m' • y) (e ▸ sub_mem
      (Submodule.smul_mem _ _ (mul_comm g i ▸ h1 g i hy)) (Submodule.smul_mem _ _ (h1 i g hy')))
    refine ⟨r, h2 i (r + m') _ ?_⟩
    have e' := congrArg θ hr
    rw [map_smul, e, map_zero, smul_sub, sub_eq_zero] at e'
    have e'' : i ^ (r + m') • g ^ r • (g ^ m • n - θ y) =
        (i * g) ^ r • i ^ m' • (g ^ m • n - θ y) := by
      rw [smul_smul, smul_smul]; congr 1; ring
    rw [e'', e']
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ hy')
  choose r hr using key
  let R := Finset.univ.sup r
  have h0 : g ^ R • (g ^ m • n - θ y) = 0 := h3 t ht' _ fun i hi ↦ by
    obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le' (Finset.le_sup (f := r) (Finset.mem_univ ⟨i, hi⟩))
    rw [show R = c + r ⟨i, hi⟩ from hc, pow_add, mul_smul]
    exact Submodule.smul_mem _ _ (hr ⟨i, hi⟩)
  refine ⟨R + m, g ^ R • y, ?_⟩
  rw [smul_sub, sub_eq_zero] at h0
  rw [map_smul, ← h0, pow_add, mul_smul]

end Glue

section Affine

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {k : Type} [CommRing k] {X : Scheme.{0}} (s : X ⟶ Sp k) (j : ℕ)

instance secModule (F : X.Modules) (U : X.Opens) : Module (Sec s U) Γ(F, U) :=
  inferInstanceAs (Module Γ(X, U) Γ(F, U))

def toOm (U : X.Opens) : OmU s U j →ₗ[Sec s U] Γ(Omega s j, U) := ((toOmega s j).app (op U)).hom

theorem toOm_apply (U : X.Opens) (x : OmU s U j) : toOm s j U x = (toOmega s j).app (op U) x := rfl

theorem res_toOm {U V : X.Opens} (h : V ≤ U) (x : OmU s U j) :
    (Omega s j).presheaf.map (homOfLE h).op (toOm s j U x) = toOm s j V (formRes s h j x) :=
  (PresheafOfModules.naturality_apply (toOmega s j) (homOfLE h).op x).symm

theorem exists_formRes_eq_zero {U : X.Opens} {x : OmU s U j} (h : toOm s j U x = 0) {p : X}
    (hp : p ∈ U) : ∃ V : X.Opens, ∃ hV : V ≤ U, p ∈ V ∧ formRes s hV j x = 0 := by
  have hm := Presheaf.equalizerSieve_mem (Opens.grothendieckTopology X)
    (toSheafify (Opens.grothendieckTopology X) (formsPre s j).presheaf) (X := op U) x 0
    (by rw [map_zero]; exact h)
  obtain ⟨V, f, hf, hpV⟩ := hm p hp
  exact ⟨V, leOfHom f, hpV, hf.trans (map_zero _)⟩

theorem exists_toOm_eq_res {U : X.Opens} (y : Γ(Omega s j, U)) {p : X} (hp : p ∈ U) :
    ∃ V : X.Opens, ∃ hV : V ≤ U, p ∈ V ∧ ∃ x : OmU s V j,
      toOm s j V x = (Omega s j).presheaf.map (homOfLE hV).op y := by
  have hm := Presheaf.imageSieve_mem (Opens.grothendieckTopology X)
    (toSheafify (Opens.grothendieckTopology X) (formsPre s j).presheaf) (U := op U) y
  obtain ⟨V, f, ⟨x, hx⟩, hpV⟩ := hm p hp
  exact ⟨V, leOfHom f, hpV, x, hx⟩

variable {s j}

theorem formRes_basicOpen {U : X.Opens} (hU : IsAffineOpen U) (g : Sec s U) :
    (∀ y : OmU s (X.basicOpen g) j, ∃ (n : ℕ) (x : OmU s U j),
      Sec.res s (X.basicOpen_le g) g ^ n • y = formRes s (X.basicOpen_le g) j x) ∧
    ∀ x : OmU s U j, formRes s (X.basicOpen_le g) j x = 0 → ∃ n : ℕ, g ^ n • x = 0 := by
  letI : Algebra (Sec s U) (Sec s (X.basicOpen g)) :=
    (Sec.res s (X.basicOpen_le g) : Sec s U →+* Sec s (X.basicOpen g)).toAlgebra
  haveI : IsScalarTower k (Sec s U) (Sec s (X.basicOpen g)) :=
    .of_algebraMap_eq fun r ↦ ((Sec.res s (X.basicOpen_le g)).commutes r).symm
  haveI : IsLocalization.Away g (Sec s (X.basicOpen g)) := hU.isLocalization_basicOpen g
  haveI : Algebra.FormallyEtale (Sec s U) (Sec s (X.basicOpen g)) :=
    .of_isLocalization (Submonoid.powers g)
  haveI := (isLocalizedModule_iff_isBaseChange (Submonoid.powers g) _ _).2
    (isBaseChange_formLin k (Sec s U) (Sec s (X.basicOpen g)) j)
  refine ⟨fun y ↦ ?_, fun x hx ↦ ?_⟩
  · obtain ⟨⟨x, _, n, rfl⟩, hx⟩ := IsLocalizedModule.surj (Submonoid.powers g)
      (formLin k (Sec s U) (Sec s (X.basicOpen g)) j) y
    refine ⟨n, x, Eq.trans ?_ hx⟩
    rw [← map_pow]
    exact algebraMap_smul _ (g ^ n) y
  · obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalizedModule.eq_zero_iff (Submonoid.powers g)
      (formLin k (Sec s U) (Sec s (X.basicOpen g)) j)).1 hx
    exact ⟨n, hn⟩

theorem span_eq_top_of_forall_mem {U : X.Opens} (hU : IsAffineOpen U) {t : Set (Sec s U)}
    (h : ∀ p ∈ U, ∃ g ∈ t, p ∈ X.basicOpen (U := U) g) : Ideal.span t = ⊤ :=
  (hU.self_le_iSup_basicOpen_iff (s := t)).1 fun p hp ↦
    have ⟨g, hg, hp'⟩ := h p hp
    Opens.mem_iSup.2 ⟨⟨g, hg⟩, hp'⟩

theorem toOm_injective {U : X.Opens} (hU : IsAffineOpen U) : Function.Injective (toOm s j U) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx ↦ ?_
  refine Submodule.mem_of_span_eq_top_of_smul_pow_mem (⊥ : Submodule (Sec s U) _)
    {g | ∃ n : ℕ, g ^ n • x = 0} (span_eq_top_of_forall_mem hU fun p hp ↦ ?_) x fun g ↦ g.2
  obtain ⟨V, hV, hpV, h0⟩ := exists_formRes_eq_zero s j hx hp
  obtain ⟨g, hg, hpg⟩ := hU.exists_basicOpen_le ⟨p, hpV⟩ hp
  refine ⟨g, (formRes_basicOpen hU g).2 x ?_, hpg⟩
  rw [← formRes_formRes s hV hg, h0, map_zero]

theorem toOm_surjective {U : X.Opens} (hU : IsAffineOpen U) : Function.Surjective (toOm s j U) := by
  let Z : Sec s U → Submodule (Sec s U) Γ(Omega s j, U) := fun g ↦
    (LinearMap.ker (QCoh.resBasicOpen (Omega s j) (U := U) (show Γ(X, U) from g)) : Submodule Γ(X, U) _)
  have hZ : ∀ g n, n ∈ Z g ↔
      (Omega s j).presheaf.map (homOfLE (X.basicOpen_le (U := U) g)).op n = 0 := fun _ _ ↦ Iff.rfl
  have hs : ∀ (V : X.Opens) (h : V ≤ U) (g : Sec s U) (n : Γ(Omega s j, U)),
      (Omega s j).presheaf.map (homOfLE h).op (g • n) =
        Sec.res s h g • (Omega s j).presheaf.map (homOfLE h).op n :=
    fun V h g n ↦ Scheme.Modules.map_smul _ _ _ _
  refine surjective_of_locally_surjective _ Z (fun g h n hn ↦ ?_) (fun g m n hn ↦ ?_)
    (fun t ht n hn ↦ ?_) (fun g y hy ↦ ?_) fun n ↦ span_eq_top_of_forall_mem hU fun p hp ↦ ?_
  · have e : X.basicOpen (U := U) (g * h) ≤ X.basicOpen (U := U) g :=
      (X.basicOpen_mul (U := U) g h).trans_le inf_le_left
    rw [hZ, ← QCoh.res_res _ (X.basicOpen_le (U := U) g) e, (hZ _ _).1 hn, map_zero]
  · rw [hZ, hs, map_pow] at hn
    have hu : IsUnit (Sec.res s (X.basicOpen_le (U := U) g) g) :=
      X.toRingedSpace.isUnit_res_basicOpen g
    exact ((hu.pow m).smul_eq_zero).1 hn
  · refine TopCat.Sheaf.eq_of_locally_eq' (⟨_, (Omega s j).isSheaf⟩ : TopCat.Sheaf Ab X)
      (fun g : t ↦ X.basicOpen (U := U) g.1) U (fun g ↦ homOfLE (X.basicOpen_le _))
      ((hU.self_le_iSup_basicOpen_iff (s := t)).2 ht) n 0 fun g ↦ ?_
    exact ((hZ _ _).1 (hn g g.2)).trans (map_zero _).symm
  · rw [hZ, res_toOm] at hy
    exact (formRes_basicOpen hU g).2 y
      (toOm_injective (hU.basicOpen g) (hy.trans (map_zero _).symm))
  · obtain ⟨V, hV, hpV, x, hx⟩ := exists_toOm_eq_res s j n hp
    obtain ⟨g, hg, hpg⟩ := hU.exists_basicOpen_le ⟨p, hpV⟩ hp
    obtain ⟨m, y, hy⟩ := (formRes_basicOpen (s := s) hU g).1 (formRes s hg j x)
    refine ⟨show Sec s U from g, ⟨m, y, (hZ _ _).2 ?_⟩, hpg⟩
    rw [map_sub, hs, res_toOm, ← hy, map_smul, ← res_toOm, hx, QCoh.res_res, map_pow, sub_self]

variable (s j)

theorem toOm_bijective {U : X.Opens} (hU : IsAffineOpen U) : Function.Bijective (toOm s j U) :=
  ⟨toOm_injective hU, toOm_surjective hU⟩

def toOmEquiv {U : X.Opens} (hU : IsAffineOpen U) : OmU s U j ≃ₗ[Sec s U] Γ(Omega s j, U) :=
  LinearEquiv.ofBijective _ (toOm_bijective s j hU)

@[simp] theorem toOmEquiv_apply {U : X.Opens} (hU : IsAffineOpen U) (x : OmU s U j) :
    toOmEquiv s j hU x = toOm s j U x := rfl

instance isQuasicoherent_Omega : (Omega s j).IsQuasicoherent := by
  refine (QCoh.isQuasicoherent_iff_forall_affine _).2 fun U hU g ↦
    (QCoh.isLocalizedModule_resBasicOpen_iff _ g).2 ⟨fun y ↦ ?_, fun t ht ↦ ?_⟩
  · obtain ⟨y, rfl⟩ := toOm_surjective (hU.basicOpen g) y
    obtain ⟨n, x, hx⟩ := (formRes_basicOpen (s := s) hU g).1 y
    refine ⟨n, toOm s j U x, ?_⟩
    rw [res_toOm, ← hx, map_smul]
    rfl
  · obtain ⟨x, rfl⟩ := toOm_surjective hU t
    rw [res_toOm] at ht
    obtain ⟨n, hn⟩ := (formRes_basicOpen (s := s) hU g).2 x
      (toOm_injective (hU.basicOpen g) (ht.trans (map_zero _).symm))
    exact ⟨n, ((toOm s j U).map_smul _ x).symm.trans ((congrArg _ hn).trans (map_zero _))⟩

end Affine

section HomOfAffine

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

variable {X : Scheme.{0}} {G F : X.Modules}

theorem section_ext_affine {U : X.Opens} {a b : Γ(F, U)}
    (h : ∀ (V : X.Opens) (_ : IsAffineOpen V) (hV : V ≤ U),
      F.presheaf.map (homOfLE hV).op a = F.presheaf.map (homOfLE hV).op b) : a = b :=
  TopCat.Sheaf.eq_of_locally_eq' (⟨_, F.isSheaf⟩ : TopCat.Sheaf Ab X)
    (fun V : {V : X.Opens // IsAffineOpen V ∧ V ≤ U} ↦ V.1) U (fun V ↦ homOfLE V.2.2)
    (fun p hp ↦
      have ⟨V, h1, h2, h3⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens hp
      Opens.mem_iSup.2 ⟨⟨V, h1, h3⟩, h2⟩) a b fun V ↦ h V.1 V.2.1 V.2.2

theorem isBasis_range_affine (X : Scheme.{0}) :
    Opens.IsBasis (Set.range fun U : X.affineOpens ↦ U.1) := by
  rw [Subtype.range_coe]; exact X.isBasis_affineOpens

variable (φ : ∀ U : X.affineOpens, Γ(G, U.1) →ₗ[Γ(X, U.1)] Γ(F, U.1))
  (hφ : ∀ (U V : X.affineOpens) (h : V.1 ≤ U.1) (x : Γ(G, U.1)),
    F.presheaf.map (homOfLE h).op (φ U x) = φ V (G.presheaf.map (homOfLE h).op x))

def preHomOfAffine : G.presheaf ⟶ F.presheaf :=
  TopCat.Sheaf.restrictHomEquivHom G.presheaf (⟨_, F.isSheaf⟩ : TopCat.Sheaf Ab X)
    (isBasis_range_affine X)
    { app U := AddCommGrpCat.ofHom (φ U.unop).toAddMonoidHom
      naturality U V i := AddCommGrpCat.ext fun x ↦ (hφ U.unop V.unop (leOfHom i.unop.hom) x).symm }

theorem preHomOfAffine_app (U : X.affineOpens) (x : Γ(G, U.1)) :
    (preHomOfAffine φ hφ).app (op U.1) x = φ U x :=
  congrArg (fun q ↦ q.hom x) (TopCat.Sheaf.extend_hom_app G.presheaf
    (⟨_, F.isSheaf⟩ : TopCat.Sheaf Ab X) (isBasis_range_affine X) _ U)

def homOfAffine : G ⟶ F :=
  SheafOfModules.Hom.mk <| PresheafOfModules.homMk (preHomOfAffine φ hφ) fun U r x ↦ by
    refine section_ext_affine (F := F) (U := U.unop) fun V hV h ↦ ?_
    have n : ∀ y : Γ(G, U.unop), F.presheaf.map (homOfLE h).op ((preHomOfAffine φ hφ).app U y) =
        φ ⟨V, hV⟩ (G.presheaf.map (homOfLE h).op y) := fun y ↦
      (ConcreteCategory.congr_hom ((preHomOfAffine φ hφ).naturality (homOfLE h).op) y).symm.trans
        (preHomOfAffine_app φ hφ ⟨V, hV⟩ _)
    exact (n _).trans (((congrArg (φ ⟨V, hV⟩) (Scheme.Modules.map_smul G _ r x)).trans
      ((φ ⟨V, hV⟩).map_smul _ _)).trans
        ((Scheme.Modules.map_smul F _ r _).trans (congrArg _ (n x))).symm)

theorem homOfAffine_app (U : X.affineOpens) (x : Γ(G, U.1)) :
    (homOfAffine φ hφ).app U.1 x = φ U x := preHomOfAffine_app φ hφ U x

omit φ hφ in

theorem hom_ext_affine {a b : G ⟶ F}
    (h : ∀ U : X.Opens, IsAffineOpen U → ∀ x, a.app U x = b.app U x) : a = b := by
  ext U x
  refine section_ext_affine fun V hV e ↦ ?_
  have n : ∀ c : G ⟶ F, F.presheaf.map (homOfLE e).op (c.app U x) =
      c.app V (G.presheaf.map (homOfLE e).op x) := fun c ↦
    (ConcreteCategory.congr_hom (c.mapPresheaf.naturality (homOfLE e).op) x).symm
  exact (n a).trans ((h V hV _).trans (n b).symm)

end HomOfAffine

end GlobalTheory.HodgeCoh
