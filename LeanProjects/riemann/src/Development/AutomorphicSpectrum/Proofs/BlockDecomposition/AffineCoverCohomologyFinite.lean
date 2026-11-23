import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Coords
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperFiniteness
import GroundTheory.ArithmeticGeometry.SchemeCohomology.CechSeparated
import GroundTheory.ArithmeticGeometry.SchemeCohomology.CechNaturality.NaturalLeray
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSheafSecPresheaf

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.VBGlue

open GroundTheory.Arith.SchemeCoh

variable {X : Scheme.{0}} {ι : Type} {U : ι → X.Opens} {κ : ι → Type} [∀ α, Fintype (κ α)]
  {g : ∀ α β, κ α → κ β → Γ(X, U α ⊓ U β)}

theorem isQuasicoherent_toMod (hc : Coc g) (haff : ∀ α, IsAffineOpen (U α)) (hU : iSup U = ⊤) :
    (toMod g).IsQuasicoherent := by
  refine isQuasicoherent_of_affineCover (toMod g) U haff hU ?_ ?_
  · intro α f m
    have hD : X.basicOpen f ≤ U α := X.basicOpen_le f
    have := (haff α).isLocalization_basicOpen f
    obtain ⟨⟨b, e, rfl⟩, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (Submonoid.powers f)
      (coord g α hD (show secGroup g (X.basicOpen f) from m))
    choose a ha using hb
    refine ⟨e, (ofCoord hc α le_rfl a : secGroup g (U α)), ?_⟩
    change secRes g hD (ofCoord hc α le_rfl a) = (rs hD f ^ e) • (show secGroup g (X.basicOpen f) from m)
    refine sec_ext_coord hc α hD (funext fun k => ?_)
    rw [coord_res g hD α le_rfl hD, coord_ofCoord]
    have h1 := congrFun ((coordEquiv hc α hD).map_smul (rs hD f ^ e) (show secGroup g (X.basicOpen f) from m)) k
    refine Eq.trans ?_ h1.symm
    have h2 := ha k
    rw [Algebra.smul_def, map_pow] at h2
    exact h2
  · intro α f m hm
    have hD : X.basicOpen f ≤ U α := X.basicOpen_le f
    have := (haff α).isLocalization_basicOpen f
    have hz : ∀ k, ∃ e : ℕ, f ^ e * coord g α le_rfl (show secGroup g (U α) from m) k = 0 := fun k => by
      have h0 : algebraMap Γ(X, U α) Γ(X, X.basicOpen f) (coord g α le_rfl (show secGroup g (U α) from m) k) = 0 := by
        have h1 := coord_res g hD α le_rfl hD (show secGroup g (U α) from m) k
        have h2 : secRes g hD (show secGroup g (U α) from m) = 0 := hm
        rw [h2] at h1
        exact h1.symm.trans (congrFun (map_zero (coordEquiv hc α hD)) k)
      obtain ⟨⟨_, e, rfl⟩, he⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers f) _ _).1 h0
      exact ⟨e, he⟩
    choose e he using hz
    refine ⟨∑ k, e k, ?_⟩
    refine (show (f ^ (∑ k, e k)) • (show secGroup g (U α) from m) = 0 from ?_)
    refine sec_ext_coord hc α le_rfl (funext fun k => ?_)
    have h1 := congrFun ((coordEquiv hc α le_rfl).map_smul (f ^ (∑ k, e k)) (show secGroup g (U α) from m)) k
    refine h1.trans ?_
    have h3 := congrFun (map_zero (coordEquiv hc α le_rfl)) k
    refine Eq.trans ?_ h3.symm
    obtain ⟨c, hc'⟩ := Nat.exists_eq_add_of_le (Finset.single_le_sum (f := e) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k))
    change f ^ (∑ k, e k) * coord g α le_rfl (show secGroup g (U α) from m) k = 0
    rw [hc', pow_add, mul_comm (f ^ e k), mul_assoc, he k, mul_zero]

theorem isCoherent_toMod (hc : Coc g) (haff : ∀ α, IsAffineOpen (U α)) (hU : iSup U = ⊤) :
    IsCoherent (toMod g) := by
  have := isQuasicoherent_toMod hc haff hU
  refine isCoherent_of_affineCover (toMod g) U haff hU fun α => ?_
  exact Module.Finite.equiv (coordEquiv hc α le_rfl).symm

end GlobalTheory.CompanionTheory.VBGlue

namespace GlobalTheory.CompanionTheory.VBGlue

open GroundTheory.Arith.SchemeCoh

universe w

section Transfer

variable {O : Type} [CommRing O] {Y : TopCat.{0}} {ι : Type} {P : (Opens Y)ᵒᵖ ⥤ AddCommGrpCat.{0}}
  {U : ι → Opens Y}

theorem symm_mem_B (K : Cx.{w} O) (T : ∀ n, K.X n ≃+ Cochain P U n)
    (hd : ∀ n x, T (n + 1) (K.d n x) = d P U n (T n x)) (p : ℕ) (y : Cochain P U p)
    (hy : y ∈ coboundaries P U p) : (T p).symm y ∈ K.B p := by
  cases p with
  | zero =>
    rw [coboundaries_zero, AddSubgroup.mem_bot] at hy
    subst hy
    rw [map_zero]
    exact Submodule.zero_mem _
  | succ p =>
    rw [coboundaries_succ] at hy
    obtain ⟨τ, rfl⟩ := hy
    refine ⟨(T p).symm τ, ?_⟩
    apply (T (p + 1)).injective
    rw [hd, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

theorem finite_H_of_cochain (K : Cx.{w} O) (T : ∀ n, K.X n ≃+ Cochain P U n)
    (hd : ∀ n x, T (n + 1) (K.d n x) = d P U n (T n x)) (p : ℕ) (φ : O → (P ⟶ P))
    [Module O (cechH P U p)] (hsm : ∀ c y, c • y = cechHMap U (φ c) p y)
    (hT : ∀ c x, T p (c • x) = push U (φ c) p (T p x)) [Module.Finite O (cechH P U p)] :
    Module.Finite O (K.H p) := by
  have hz : ∀ σ : cocycles P U p, K.d p ((T p).symm σ.1) = 0 := fun σ => by
    apply (T (p + 1)).injective
    rw [hd, AddEquiv.apply_symm_apply, map_zero]
    exact σ.2
  let g₀ : cocycles P U p →+ K.Z p :=
    { toFun := fun σ => ⟨(T p).symm σ.1, hz σ⟩
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun σ τ => Subtype.ext (map_add _ _ _) }
  let f : cocycles P U p →+ K.H p := (Submodule.mkQ _).toAddMonoidHom.comp g₀
  have hf : (coboundaries P U p).addSubgroupOf (cocycles P U p) ≤ f.ker := by
    intro σ hσ
    rw [AddSubgroup.mem_addSubgroupOf] at hσ
    rw [AddMonoidHom.mem_ker]
    exact (Submodule.Quotient.mk_eq_zero _).2 (symm_mem_B K T hd p _ hσ)
  let Ψ : cechH P U p →+ K.H p := QuotientAddGroup.lift _ f hf
  have hΨ : ∀ σ (hσ : d P U p σ = 0), Ψ (cls σ hσ) =
      K.cls ((T p).symm σ) (hz ⟨σ, (mem_cocycles σ).2 hσ⟩) := fun σ hσ => rfl
  let L : cechH P U p →ₗ[O] K.H p :=
    { toFun := Ψ
      map_add' := map_add Ψ
      map_smul' := fun c y => by
        obtain ⟨σ, hσ, rfl⟩ := exists_cls y
        have h1 : (T p).symm (push U (φ c) p σ) = c • (T p).symm σ := by
          apply (T p).injective
          rw [AddEquiv.apply_symm_apply, hT, AddEquiv.apply_symm_apply]
        rw [hsm, cechHMap_cls, hΨ, hΨ, RingHom.id_apply]
        change Submodule.Quotient.mk _ = c • Submodule.Quotient.mk _
        rw [← Submodule.Quotient.mk_smul]
        exact congrArg _ (Subtype.ext h1) }
  refine Module.Finite.of_surjective L fun y => ?_
  obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  have hσ : d P U p (T p x) = 0 := by
    rw [← hd]
    exact (congrArg (T (p + 1)) hx).trans (map_zero _)
  refine ⟨cls (T p x) hσ, ?_⟩
  exact (hΨ _ hσ).trans (congrArg _ (Subtype.ext ((T p).symm_apply_apply x)))

end Transfer

section VBpart

attribute [local instance] VB.fin

variable {X : Scheme.{0}}

theorem sum_rs_eq {C W : X.Opens} (h : W ≤ C) {n : Type} [Fintype n] (A B : n → Γ(X, C))
    (hAB : ∀ v : n → Γ(X, C), ∑ k, A k * v k = ∑ k, B k * v k) (v : n → Γ(X, W)) :
    ∑ k, rs h (A k) * v k = ∑ k, rs h (B k) * v k := by
  classical
  have : A = B := funext fun j => by
    simpa [Pi.single_apply] using hAB (Pi.single j 1)
  rw [this]

variable {O : Type} [CommRing O] {str : ∀ V : X.Opens, O →+* Γ(X, V)} {ι : Type} {U : ι → X.Opens}
  {K : Cos.{w} O} (V : VB str U K)

theorem exists_e (n : ℕ) (a : Fin (n + 1)) (i : Fin (n + 1) → ι) (v : V.κ (i a) → Γ(X, capO U i)) :
    ∃ x, V.e n a x i = v := by
  classical
  refine ⟨(V.e n a).symm (Pi.single i v), ?_⟩
  rw [AddEquiv.apply_symm_apply, Pi.single_eq_same]

theorem coc3 (i : Fin 3 → ι) (W : X.Opens) (hW : W ≤ capO U i) (h₁ : W ≤ U (i 0) ⊓ U (i 1))
    (h₂ : W ≤ U (i 1) ⊓ U (i 2)) (h₃ : W ≤ U (i 0) ⊓ U (i 2)) (v : V.κ (i 2) → Γ(X, W)) (k : V.κ (i 0)) :
    ∑ k', rs h₁ (V.g (i 0) (i 1) k k') * ∑ k'', rs h₂ (V.g (i 1) (i 2) k' k'') * v k'' =
      ∑ k'', rs h₃ (V.g (i 0) (i 2) k k'') * v k'' := by
  have a01 := le_inf (capO_le U i 0) (capO_le U i 1)
  have a12 := le_inf (capO_le U i 1) (capO_le U i 2)
  have a02 := le_inf (capO_le U i 0) (capO_le U i 2)
  have key := sum_rs_eq hW
    (fun k'' => ∑ k', rs a01 (V.g (i 0) (i 1) k k') * rs a12 (V.g (i 1) (i 2) k' k''))
    (fun k'' => rs a02 (V.g (i 0) (i 2) k k'')) (fun w => by
      obtain ⟨x, rfl⟩ := exists_e V 2 2 i w
      rw [← V.e_chg 2 0 2 x i k, V.e_chg 2 0 1 x i k]
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k' _ => ?_
      rw [V.e_chg 2 1 2 x i k', Finset.mul_sum]
      exact Finset.sum_congr rfl fun k'' _ => mul_assoc _ _ _) v
  simp only [map_sum, map_mul, rs_trans, Finset.sum_mul] at key
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Eq.trans (Finset.sum_congr rfl fun k'' _ => Finset.sum_congr rfl fun k' _ => (mul_assoc _ _ _).symm) key

theorem coc_of_VB : Coc V.g := by
  classical
  constructor
  · intro α W h v k
    have hW : W ≤ capO U (fun _ : Fin 1 => α) := le_iInf fun _ => h.trans inf_le_left
    have key := sum_rs_eq hW
      (fun k' => rs (le_inf (capO_le U (fun _ : Fin 1 => α) 0) (capO_le U (fun _ : Fin 1 => α) 0)) (V.g α α k k'))
      (fun k' => if k = k' then 1 else 0) (fun w => by
        obtain ⟨x, rfl⟩ := exists_e V 0 0 (fun _ : Fin 1 => α) w
        have := V.e_chg 0 0 0 x (fun _ : Fin 1 => α) k
        simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
        exact this.symm) v
    have e2 : ∀ k', rs hW (if k = k' then (1 : Γ(X, capO U (fun _ : Fin 1 => α))) else 0) =
        if k = k' then 1 else 0 := fun k' => by split_ifs <;> simp
    simp only [rs_trans, e2, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true] at key
    exact key
  · intro α β γ W h₁ h₂ h₃ v k
    refine coc3 V ![α, β, γ] W (le_iInf fun a => ?_) h₁ h₂ h₃ v k
    fin_cases a
    exacts [h₁.trans inf_le_left, h₁.trans inf_le_right, h₂.trans inf_le_right]

end VBpart

end GlobalTheory.CompanionTheory.VBGlue

namespace GlobalTheory.CompanionTheory.VBGlue

open GroundTheory.Arith.SchemeCoh

universe w

theorem inter_le_capO {X : Scheme.{0}} {ι : Type} (U : ι → X.Opens) {n : ℕ} (i : Fin n → ι) :
    inter (X := X.toTopCat) U i ≤ capO U i := (inter_eq_iInf U i).le

theorem capO_le_inter {X : Scheme.{0}} {ι : Type} (U : ι → X.Opens) {n : ℕ} (i : Fin n → ι) :
    capO U i ≤ inter (X := X.toTopCat) U i := (inter_eq_iInf U i).ge

theorem secRes_secRes {X : Scheme.{0}} {ι : Type} {U : ι → X.Opens} {κ : ι → Type} [∀ α, Fintype (κ α)]
    (g : ∀ α β, κ α → κ β → Γ(X, U α ⊓ U β)) {A B C : X.Opens} (h : B ≤ A) (h' : C ≤ B) (h'' : C ≤ A)
    (s : secGroup g A) : secRes g h' (secRes g h s) = secRes g h'' s :=
  Subtype.ext <| funext fun α => funext fun k => rs_rs _ _ _ _

theorem secRes_self {X : Scheme.{0}} {ι : Type} {U : ι → X.Opens} {κ : ι → Type} [∀ α, Fintype (κ α)]
    (g : ∀ α β, κ α → κ β → Γ(X, U α ⊓ U β)) {A : X.Opens} (h : A ≤ A) (s : secGroup g A) :
    secRes g h s = s :=
  Subtype.ext <| funext fun α => funext fun k => rs_self _ _

section Bridge

attribute [local instance] VB.fin

variable {X : Scheme.{0}} {O : Type} [CommRing O] {str : ∀ V : X.Opens, O →+* Γ(X, V)} {ι : Type}
  {U : ι → X.Opens} {K : Cos.{w} O} (V : VB str U K)

def toSec (n : ℕ) : K.X n ≃+ ∀ i : Fin (n + 1) → ι, secGroup V.g (capO U i) :=
  (V.e n 0).trans (AddEquiv.piCongrRight fun i =>
    (coordEquiv (coc_of_VB V) (i 0) (capO_le U i 0)).symm.toAddEquiv)

theorem coord_toSec (n : ℕ) (x : K.X n) (i : Fin (n + 1) → ι) (a : Fin (n + 1)) :
    coord V.g (i a) (capO_le U i a) (toSec V n x i) = V.e n a x i := by
  funext k
  rw [coord_change V.g (i a) (i 0) _ (capO_le U i 0) (le_inf (capO_le U i a) (capO_le U i 0)),
    V.e_chg n a 0 x i k]
  refine Finset.sum_congr rfl fun k' _ => ?_
  have : coord V.g (i 0) (capO_le U i 0) (toSec V n x i) = V.e n 0 x i :=
    (coordEquiv (coc_of_VB V) (i 0) (capO_le U i 0)).apply_symm_apply _
  rw [this]

theorem toSec_δ (n : ℕ) (b : Fin (n + 2)) (x : K.X n) (i : Fin (n + 2) → ι) :
    toSec V (n + 1) (K.δ n b x) i =
      secRes V.g (capO_comp U i b.succAbove) (toSec V n x (i ∘ b.succAbove)) := by
  refine sec_ext_coord (coc_of_VB V) (i (b.succAbove 0)) (capO_le U i _) (funext fun k => ?_)
  rw [coord_toSec, V.e_δ n 0 b x i k,
    coord_res V.g (capO_comp U i b.succAbove) (i (b.succAbove 0)) (capO_le U (i ∘ b.succAbove) 0)]
  exact congrArg (rs _) (congrFun (coord_toSec V n x (i ∘ b.succAbove) 0) k).symm

theorem toSec_smul (n : ℕ) (c : O) (x : K.X n) (i : Fin (n + 1) → ι) :
    toSec V n (c • x) i = str (capO U i) c • toSec V n x i := by
  refine sec_ext_coord (coc_of_VB V) (i 0) (capO_le U i 0) (funext fun k => ?_)
  rw [coord_toSec]
  have h1 := congrFun ((coordEquiv (coc_of_VB V) (i 0) (capO_le U i 0)).map_smul (str (capO U i) c) (toSec V n x i)) k
  refine Eq.trans ?_ h1.symm
  rw [V.e_smul]
  change _ = _ * coord V.g (i 0) (capO_le U i 0) (toSec V n x i) k
  rw [coord_toSec]

def toCochain (n : ℕ) : K.X n ≃+ Cochain (modulesAb (toMod V.g)).obj U n where
  toFun x i := secRes V.g (inter_le_capO U i) (toSec V n x i)
  invFun y := (toSec V n).symm fun i => secRes V.g (capO_le_inter U i) (y i)
  left_inv x := by
    refine (AddEquiv.symm_apply_eq _).2 (funext fun i => ?_)
    exact (secRes_secRes V.g (inter_le_capO U i) (capO_le_inter U i) le_rfl _).trans (secRes_self V.g le_rfl _)
  right_inv y := funext fun i => by
    have h := congrFun ((toSec V n).apply_symm_apply (fun i => secRes V.g (capO_le_inter U i) (y i))) i
    exact (congrArg (secRes V.g (inter_le_capO U i)) h).trans
      ((secRes_secRes V.g (capO_le_inter U i) (inter_le_capO U i) le_rfl _).trans (secRes_self V.g le_rfl _))
  map_add' a b := funext fun i => by
    rw [map_add]
    exact map_add (secRes V.g (inter_le_capO U i)) _ _

end Bridge

theorem str_eq {O : Type} [CommRing O] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (W : X.Opens) (c : O) :
    ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫ q.appLE ⊤ W le_top).hom c =
      rs (le_top : W ≤ ⊤) (q.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom c)) := rfl

attribute [local instance] VB.fin algebraOfOver in

theorem finite_H_cx : ∀ {O : Type} [CommRing O] [IsNoetherianRing O] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) [IsProper q]
    {ι : Type} [Fintype ι] (U : ι → X.Opens) (hU : (⨆ α, U α) = ⊤) (ha : ∀ n (i : Fin (n + 1) → ι), IsAffineOpen (capO U i))
    (K : Cos.{1} O) (V : VB (fun W => ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫ q.appLE ⊤ W le_top).hom) U K) (p : ℕ),
    Module.Finite O (K.cx.H p) := by
  intro O _ _ X q _ ι _ U hU ha K V p
  letI : X.Over (Spec (.of O)) := ⟨q⟩
  have hprop : IsProper (X ↘ Spec (.of O)) := ‹IsProper q›
  have hc := coc_of_VB V
  have haff : ∀ α, IsAffineOpen (U α) := fun α => by
    have := ha 0 (fun _ => α)
    have e : capO U (fun _ : Fin 1 => α) = U α := iInf_const
    rwa [e] at this
  have hcoh := isCoherent_toMod hc haff hU
  have := hcoh.1
  have hfin := finite_H_of_isProper (A := O) (toMod V.g) hcoh p
  have hfinC : Module.Finite O (cechH (modulesAb (toMod V.g)).obj U p) :=
    Module.Finite.equiv (cechHLinearEquivH U hU ha O (toMod V.g) p).symm
  refine finite_H_of_cochain (P := (modulesAb (toMod V.g)).obj) (U := U) K.cx (fun n => toCochain V n) ?_ p
    (fun c => (modulesAbMap (smulHom (toMod V.g) (algebraMap O Γ(X, ⊤) c))).hom) (fun _ _ => rfl) ?_
  · intro n x
    funext i
    rw [d_apply]
    change secRes V.g (inter_le_capO U i) (toSec V (n + 1) (K.d n x) i) = _
    rw [Cos.d_apply, map_sum, Finset.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_zsmul, Pi.smul_apply, map_zsmul, toSec_δ]
    have H := (inter_le_comp (X := X.toTopCat) U i k.succAbove).trans (inter_le_capO U (i ∘ k.succAbove))
    exact congrArg _ ((secRes_secRes V.g _ _ H _).trans
      (secRes_secRes V.g (inter_le_capO U (i ∘ k.succAbove)) (inter_le_comp (X := X.toTopCat) U i k.succAbove) H _).symm)
  · intro c x
    funext i
    change secRes V.g (inter_le_capO U i) (toSec V p (c • x) i) = _
    rw [toSec_smul, secRes_smul]
    have hs : rs (inter_le_capO U i) (((Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫ q.appLE ⊤ (capO U i) le_top).hom c) =
        restrictTop (inter (X := X.toTopCat) U i) (algebraMap O Γ(X, ⊤) c) := by
      rw [str_eq, rs_trans]
      rfl
    rw [hs]
    rfl

end GlobalTheory.CompanionTheory.VBGlue
