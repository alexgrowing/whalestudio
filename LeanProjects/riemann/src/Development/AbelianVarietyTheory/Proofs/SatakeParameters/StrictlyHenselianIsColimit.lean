import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStrictHenselisation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgHomExtLocalization
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndEtaleLocalizedPiecesTrans
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStrictHenselisationOfDirectedUnion
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRingHomOfIsStrictHenselisation
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

noncomputable section
open IsLocalRing

namespace GlobalTheory.SHColim

def Pieces (R S : Type) [CommRing R] [CommRing S] [Algebra R S] : Prop :=
  ∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra R S),
    Monotone Si ∧ (∀ s : S, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (A : Type) (_ : CommRing A) (_ : Algebra R A)
      (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] Si i)

structure SHD (R : Type) [CommRing R] [IsLocalRing R] (Ω : Type) [Field Ω] [Algebra (ResidueField R) Ω] where
  S : Type
  [ring : CommRing S]
  [alg : Algebra R S]
  [hens : HenselianLocalRing S]
  [loc : IsLocalHom (algebraMap R S)]
  sep : IsSepClosed (ResidueField S)
  e : ResidueField S ≃ₐ[ResidueField R] Ω
  pieces : Pieces R S

attribute [instance] SHD.ring SHD.alg SHD.hens SHD.loc

theorem SHD.nonempty (R : Type) [CommRing R] [IsLocalRing R] (Ω : Type) [Field Ω]
    [Algebra (ResidueField R) Ω] [IsSepClosure (ResidueField R) Ω] : Nonempty (SHD R Ω) := by
  obtain ⟨S, _, _, _, _, hsep, -, -, ⟨e⟩, hp⟩ := GlobalTheory.exists_strictHenselisation R Ω
  exact ⟨{ S := S, sep := hsep, e := e, pieces := hp }⟩

section
variable (A : Type) [CommRing A] [HenselianLocalRing A] [IsSepClosed (ResidueField A)]

abbrev pB (B : Subalgebra ℤ A) : Ideal B := (maximalIdeal A).comap (algebraMap B A)

abbrev RB (B : Subalgebra ℤ A) : Type := Localization.AtPrime (pB A B)

theorem isUnit_of_notMem (B : Subalgebra ℤ A) (y : (pB A B).primeCompl) : IsUnit (algebraMap B A y) := by
  by_contra h
  exact y.2 ((mem_maximalIdeal _).2 h)

def toA (B : Subalgebra ℤ A) : RB A B →+* A :=
  IsLocalization.lift (M := (pB A B).primeCompl) (isUnit_of_notMem A B)

@[simp] theorem toA_algebraMap (B : Subalgebra ℤ A) (b : B) : toA A B (algebraMap B (RB A B) b) = b :=
  IsLocalization.lift_eq _ _

theorem toA_injective (B : Subalgebra ℤ A) : Function.Injective (toA A B) := by
  rw [toA, IsLocalization.lift_injective_iff]
  intro x y
  constructor
  · intro h
    rw [IsLocalization.eq_iff_exists (pB A B).primeCompl] at h
    obtain ⟨c, hc⟩ := h
    have := congrArg (algebraMap B A) hc
    simp only [map_mul] at this
    exact (isUnit_of_notMem A B c).mul_left_cancel this
  · intro h
    have : x = y := Subtype.ext h
    rw [this]

instance (B : Subalgebra ℤ A) : IsLocalHom (toA A B) := by
  constructor
  intro z hz
  obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective (pB A B).primeCompl z
  have h1 : toA A B (IsLocalization.mk' (RB A B) b s) * (algebraMap B A s) = algebraMap B A b := by
    have := congrArg (toA A B) (IsLocalization.mk'_spec (RB A B) b s)
    rwa [map_mul, toA_algebraMap, toA_algebraMap] at this
  have hb : IsUnit (algebraMap B A b) := h1 ▸ hz.mul (isUnit_of_notMem A B s)
  have hbm : b ∈ (pB A B).primeCompl := fun hm => (mem_maximalIdeal _).1 hm hb
  have h2 := IsLocalization.mk'_spec (RB A B) b s
  have h3 : IsUnit (algebraMap B (RB A B) b) := IsLocalization.map_units (RB A B) (⟨b, hbm⟩ : (pB A B).primeCompl)
  rw [← h2] at h3
  exact isUnit_of_mul_isUnit_left h3
end

section
variable (A : Type) [CommRing A] [HenselianLocalRing A] [IsSepClosed (ResidueField A)]

instance algRes (B : Subalgebra ℤ A) : Algebra (ResidueField (RB A B)) (ResidueField A) :=
  (ResidueField.map (toA A B)).toAlgebra

abbrev Om (B : Subalgebra ℤ A) : IntermediateField (ResidueField (RB A B)) (ResidueField A) :=
  separableClosure (ResidueField (RB A B)) (ResidueField A)

def sh (B : Subalgebra ℤ A) : SHD (RB A B) (Om A B) := Classical.choice (SHD.nonempty _ _)

abbrev O (B : Subalgebra ℤ A) : Type := (sh A B).S

def σ (B : Subalgebra ℤ A) : ResidueField (O A B) →+* ResidueField A :=
  (Om A B).val.toRingHom.comp (sh A B).e.toAlgHom.toRingHom

def ρ (B : Subalgebra ℤ A) : O A B →+* ResidueField A := (σ A B).comp (residue _)

theorem σ_apply (B : Subalgebra ℤ A) (x : ResidueField (O A B)) : σ A B x = ((sh A B).e x : ResidueField A) := rfl

theorem rho_alg (B : Subalgebra ℤ A) (r : RB A B) : ρ A B (algebraMap _ _ r) = residue A (toA A B r) := by
  simp only [ρ, RingHom.comp_apply, σ_apply]
  rw [← ResidueField.algebraMap_residue, AlgEquiv.commutes]
  change algebraMap (ResidueField (RB A B)) (ResidueField A) (residue _ r) = _
  exact ResidueField.map_residue (toA A B) r

theorem uniq (B : Subalgebra ℤ A) {T : Type} [CommRing T] [HenselianLocalRing T]
    (τ : ResidueField T →+* ResidueField A) (f : RB A B →+* T) (g₁ g₂ : O A B →+* T)
    (h₁ : g₁.comp (algebraMap _ _) = f) (h₂ : g₂.comp (algebraMap _ _) = f)
    (hr : τ.comp ((residue T).comp g₁) = τ.comp ((residue T).comp g₂)) : g₁ = g₂ := by
  letI : Algebra (RB A B) T := f.toAlgebra
  let G₁ : O A B →ₐ[RB A B] T := { g₁ with commutes' := fun r => DFunLike.congr_fun h₁ r }
  let G₂ : O A B →ₐ[RB A B] T := { g₂ with commutes' := fun r => DFunLike.congr_fun h₂ r }
  have hres : ∀ x, residue T (g₁ x) = residue T (g₂ x) := fun x => τ.injective (DFunLike.congr_fun hr x)
  have := (GlobalTheory.IndEtaleHensel.bijective_residue_comp (RB A B) (O A B) T (sh A B).pieces).1
    (a₁ := G₁) (a₂ := G₂) (by ext x; exact hres x)
  ext x; exact DFunLike.congr_fun this x

theorem exist (B : Subalgebra ℤ A) {T : Type} [CommRing T] [HenselianLocalRing T]
    (f : RB A B →+* T) (ψ : O A B →+* ResidueField T) (hψ : ψ.comp (algebraMap _ _) = (residue T).comp f) :
    ∃ g : O A B →+* T, g.comp (algebraMap _ _) = f ∧ (residue T).comp g = ψ := by
  letI : Algebra (RB A B) T := f.toAlgebra
  let Ψ : O A B →ₐ[RB A B] ResidueField T := { ψ with commutes' := fun r => DFunLike.congr_fun hψ r }
  obtain ⟨G, hG⟩ := (GlobalTheory.IndEtaleHensel.bijective_residue_comp (RB A B) (O A B) T (sh A B).pieces).2 Ψ
  exact ⟨G.toRingHom, RingHom.ext fun r => G.commutes r, RingHom.ext fun x => DFunLike.congr_fun hG x⟩

theorem exists_g (B : Subalgebra ℤ A) :
    ∃ g : O A B →+* A, g.comp (algebraMap _ _) = toA A B ∧ (residue A).comp g = ρ A B :=
  exist A B (toA A B) (ρ A B) (RingHom.ext fun r => rho_alg A B r)

def g (B : Subalgebra ℤ A) : O A B →+* A := (exists_g A B).choose

theorem g_alg (B : Subalgebra ℤ A) (r : RB A B) : g A B (algebraMap _ _ r) = toA A B r :=
  DFunLike.congr_fun (exists_g A B).choose_spec.1 r

theorem g_res (B : Subalgebra ℤ A) (x : O A B) : residue A (g A B x) = ρ A B x :=
  DFunLike.congr_fun (exists_g A B).choose_spec.2 x

end

section
variable (A : Type) [CommRing A] [HenselianLocalRing A] [IsSepClosed (ResidueField A)]
variable {A}

theorem pB_comap {B B' : Subalgebra ℤ A} (h : B ≤ B') :
    pB A B = (pB A B').comap (Subalgebra.inclusion h).toRingHom := by
  ext x; exact Iff.rfl

def loc {B B' : Subalgebra ℤ A} (h : B ≤ B') : RB A B →+* RB A B' :=
  Localization.localRingHom (pB A B) (pB A B') (Subalgebra.inclusion h).toRingHom (pB_comap h)

instance {B B' : Subalgebra ℤ A} (h : B ≤ B') : IsLocalHom (loc h) := by
  unfold loc; infer_instance

theorem loc_algebraMap {B B' : Subalgebra ℤ A} (h : B ≤ B') (b : B) :
    loc h (algebraMap B (RB A B) b) = algebraMap B' (RB A B') (Subalgebra.inclusion h b) :=
  Localization.localRingHom_to_map _ _ _ _ _

theorem loc_refl (B : Subalgebra ℤ A) : loc (le_refl B) = RingHom.id _ := by
  apply IsLocalization.ringHom_ext (pB A B).primeCompl
  ext b
  simp only [RingHom.comp_apply, loc_algebraMap, RingHom.id_apply]
  rfl

theorem loc_trans {B B' B'' : Subalgebra ℤ A} (h : B ≤ B') (h' : B' ≤ B'') :
    loc (h.trans h') = (loc h').comp (loc h) := by
  apply IsLocalization.ringHom_ext (pB A B).primeCompl
  ext b
  simp only [RingHom.comp_apply, loc_algebraMap]
  rfl

theorem toA_loc {B B' : Subalgebra ℤ A} (h : B ≤ B') (r : RB A B) : toA A B' (loc h r) = toA A B r := by
  have : (toA A B').comp (loc h) = toA A B := by
    apply IsLocalization.ringHom_ext (pB A B).primeCompl
    ext b
    simp only [RingHom.comp_apply, loc_algebraMap, toA_algebraMap]
    rfl
  exact DFunLike.congr_fun this r

theorem Om_le {B B' : Subalgebra ℤ A} (h : B ≤ B') (x : ResidueField A) (hx : x ∈ Om A B) : x ∈ Om A B' := by
  letI : Algebra (ResidueField (RB A B)) (ResidueField (RB A B')) := (ResidueField.map (loc h)).toAlgebra
  haveI : IsScalarTower (ResidueField (RB A B)) (ResidueField (RB A B')) (ResidueField A) := by
    refine IsScalarTower.of_algebraMap_eq fun y => ?_
    obtain ⟨r, rfl⟩ := residue_surjective y
    change ResidueField.map (toA A B) (residue _ r) =
      ResidueField.map (toA A B') (ResidueField.map (loc h) (residue _ r))
    rw [ResidueField.map_residue, ResidueField.map_residue, ResidueField.map_residue, toA_loc]
  rw [mem_separableClosure_iff] at hx ⊢
  exact IsSeparable.tower_top _ hx

def incΩ {B B' : Subalgebra ℤ A} (h : B ≤ B') : Om A B →+* Om A B' :=
  (Om A B).val.toRingHom.codRestrict (Om A B') (fun x => Om_le h _ x.2)

def ψ {B B' : Subalgebra ℤ A} (h : B ≤ B') : O A B →+* ResidueField (O A B') :=
  (sh A B').e.symm.toAlgHom.toRingHom.comp ((incΩ h).comp ((sh A B).e.toAlgHom.toRingHom.comp (residue _)))

theorem σ_ψ {B B' : Subalgebra ℤ A} (h : B ≤ B') (x : O A B) : σ A B' (ψ h x) = ρ A B x := by
  simp only [σ_apply, ψ, ρ, RingHom.comp_apply]
  simp [incΩ]

theorem exists_trans {B B' : Subalgebra ℤ A} (h : B ≤ B') :
    ∃ t : O A B →+* O A B', t.comp (algebraMap _ _) = (algebraMap _ _).comp (loc h) ∧
      (residue _).comp t = ψ h := by
  refine exist A B _ (ψ h) (RingHom.ext fun r => (σ A B').injective ?_)
  simp only [RingHom.comp_apply, σ_ψ, rho_alg]
  change _ = ρ A B' _
  rw [rho_alg, toA_loc]

def trans {B B' : Subalgebra ℤ A} (h : B ≤ B') : O A B →+* O A B' := (exists_trans h).choose

theorem trans_alg {B B' : Subalgebra ℤ A} (h : B ≤ B') :
    (trans h).comp (algebraMap _ _) = (algebraMap _ _).comp (loc h) := (exists_trans h).choose_spec.1

theorem trans_rho {B B' : Subalgebra ℤ A} (h : B ≤ B') (x : O A B) : ρ A B' (trans h x) = ρ A B x := by
  rw [← σ_ψ h, ← (exists_trans h).choose_spec.2]; rfl

theorem trans_unique {B B' : Subalgebra ℤ A} (h : B ≤ B') (u : O A B →+* O A B')
    (hu : u.comp (algebraMap _ _) = (algebraMap _ _).comp (loc h)) (hr : ∀ x, ρ A B' (u x) = ρ A B x) :
    u = trans h :=
  uniq A B (σ A B') _ u (trans h) hu (trans_alg h) (RingHom.ext fun x => by
    change ρ A B' (u x) = ρ A B' (trans h x); rw [hr, trans_rho])

theorem g_unique (B : Subalgebra ℤ A) (u : O A B →+* A) (hu : u.comp (algebraMap _ _) = toA A B)
    (hr : ∀ x, residue A (u x) = ρ A B x) : u = g A B :=
  uniq A B (RingHom.id _) (toA A B) u (g A B) hu (RingHom.ext fun r => g_alg A B r)
    (RingHom.ext fun x => by simp only [RingHom.comp_apply, RingHom.id_apply, hr, g_res])

theorem trans_refl (B : Subalgebra ℤ A) : trans (le_refl B) = RingHom.id _ :=
  (trans_unique _ _ (by rw [loc_refl]; rfl) (fun _ => rfl)).symm

theorem trans_trans {B B' B'' : Subalgebra ℤ A} (h : B ≤ B') (h' : B' ≤ B'') :
    trans (h.trans h') = (trans h').comp (trans h) := by
  refine (trans_unique _ _ ?_ ?_).symm
  · rw [RingHom.comp_assoc, trans_alg, ← RingHom.comp_assoc, trans_alg, RingHom.comp_assoc, ← loc_trans h h']
  · intro x; simp only [RingHom.comp_apply, trans_rho]

theorem g_trans {B B' : Subalgebra ℤ A} (h : B ≤ B') (x : O A B) : g A B' (trans h x) = g A B x := by
  have := g_unique B ((g A B').comp (trans h)) (by
      rw [RingHom.comp_assoc, trans_alg]; ext r; simp [g_alg, toA_loc])
    (fun x => by simp [g_res, trans_rho])
  exact DFunLike.congr_fun this x

end

section
variable {A : Type} [CommRing A] [HenselianLocalRing A] [IsSepClosed (ResidueField A)]

theorem key {B : Subalgebra ℤ A} (E : Type) [CommRing E] [Algebra (RB A B) E] [Algebra.Etale (RB A B) E]
    (ε : E →ₐ[RB A B] O A B) (a : E) (ha : g A B (ε a) = 0) :
    ∃ F : Finset A, ∀ (B' : Subalgebra ℤ A) (h : B ≤ B'), (F : Set A) ⊆ B' → trans h (ε a) = 0 := by
  classical
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := RB A B) (A := E)
  let γ : E →+* A := (g A B).comp ε.toRingHom
  refine ⟨s.image γ, fun B' h hF => ?_⟩
  have hγ : ∀ r : RB A B, γ (algebraMap _ E r) = toA A B r := fun r => by
    simp only [γ, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes, g_alg]
  have hrange : ∀ y : E, γ y ∈ (toA A B').range := by
    have : ∀ y ∈ Algebra.adjoin (RB A B) (s : Set E), γ y ∈ (toA A B').range := by
      intro y hy
      induction hy using Algebra.adjoin_induction with
      | mem x hx =>
        exact ⟨algebraMap B' (RB A B') ⟨γ x, hF (Finset.mem_image_of_mem γ hx)⟩, toA_algebraMap A B' _⟩
      | algebraMap r => exact ⟨loc h r, by rw [toA_loc, hγ]⟩
      | add x y _ _ hx hy => rw [map_add]; exact Subring.add_mem _ hx hy
      | mul x y _ _ hx hy => rw [map_mul]; exact Subring.mul_mem _ hx hy
    intro y; exact this y (hs ▸ Algebra.mem_top)
  let e' : RB A B' ≃+* (toA A B').range := RingEquiv.ofBijective (toA A B').rangeRestrict
    ⟨fun x y hxy => toA_injective A B' (congrArg Subtype.val hxy), RingHom.rangeRestrict_surjective _⟩
  let φ₀ : E →+* RB A B' := e'.symm.toRingHom.comp (γ.codRestrict _ hrange)
  have hφ₀ : ∀ y, toA A B' (φ₀ y) = γ y := fun y =>
    congrArg Subtype.val (e'.apply_symm_apply (γ.codRestrict _ hrange y))
  have hφ₀r : ∀ r : RB A B, φ₀ (algebraMap _ E r) = loc h r := fun r =>
    toA_injective A B' (by rw [hφ₀, hγ, toA_loc])
  have key := GlobalTheory.NCyc.StrictLocLift.lift_unique (algebraMap (RB A B) E) (RingHom.etale_algebraMap.2 inferInstance)
    ((algebraMap (RB A B') (O A B')).comp (loc h)) ((algebraMap (RB A B') (O A B')).comp φ₀)
    ((trans h).comp ε.toRingHom)
    (RingHom.ext fun r => by simp only [RingHom.comp_apply, hφ₀r])
    (RingHom.ext fun r => by
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
      exact DFunLike.congr_fun (trans_alg h) r)
    (RingHom.ext fun y => (σ A B').injective (by
      change ρ A B' _ = ρ A B' _
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rho_alg, hφ₀, trans_rho]
      rw [← g_res]; rfl))
  have h1 : trans h (ε a) = algebraMap (RB A B') (O A B') (φ₀ a) := (DFunLike.congr_fun key a).symm
  have h2 : φ₀ a = 0 := toA_injective A B' (by rw [hφ₀, map_zero]; exact ha)
  rw [h1, h2, map_zero]

theorem ker {B : Subalgebra ℤ A} (x : O A B) (hx : g A B x = 0) :
    ∃ F : Finset A, ∀ (B' : Subalgebra ℤ A) (h : B ≤ B'), (F : Set A) ⊆ B' → trans h x = 0 := by
  obtain ⟨ι, _, _, _, Si, -, hcov, hloc⟩ := (sh A B).pieces
  obtain ⟨i, hi⟩ := hcov x
  obtain ⟨E, _, _, _, q, _, ⟨eqv⟩⟩ := hloc i
  obtain ⟨⟨a, s⟩, hy⟩ := IsLocalization.mk'_surjective q.primeCompl (eqv.symm ⟨x, hi⟩)
  let ε : E →ₐ[RB A B] O A B :=
    (Si i).val.comp (eqv.toAlgHom.comp (IsScalarTower.toAlgHom (RB A B) E (Localization.AtPrime q)))
  have hxs : x * ε s = ε a := by
    have h1 : eqv.symm ⟨x, hi⟩ * algebraMap E (Localization.AtPrime q) s = algebraMap E _ a := by
      rw [← hy]; exact IsLocalization.mk'_spec _ a s
    have h2 := congrArg (fun z => ((eqv z : Si i) : O A B)) h1
    simp only [map_mul, AlgEquiv.apply_symm_apply, Subalgebra.coe_mul] at h2
    exact h2
  have hunit : IsUnit (ε s) :=
    (IsLocalization.map_units (Localization.AtPrime q) s).map
      ((Si i).val.comp eqv.toAlgHom)
  have ga : g A B (ε a) = 0 := by rw [← hxs, map_mul, hx, zero_mul]
  obtain ⟨F, hF⟩ := key E ε a ga
  refine ⟨F, fun B' h hFB => ?_⟩
  have h3 : trans h x * trans h (ε s) = 0 := by rw [← map_mul, hxs, hF B' h hFB]
  exact (hunit.map (trans h)).mul_left_eq_zero.mp h3

end

section
variable {A : Type} [CommRing A] [HenselianLocalRing A] [IsSepClosed (ResidueField A)]

theorem isLocalHom_of_le {X Y : Type} [CommRing X] [IsLocalRing X] [CommRing Y] [IsLocalRing Y] (f : X →+* Y)
    (h : ∀ x ∈ maximalIdeal X, f x ∈ maximalIdeal Y) : IsLocalHom f :=
  ⟨fun a ha => by
    by_contra hna
    exact ((mem_maximalIdeal _).1 (h a ((mem_maximalIdeal _).2 hna))) ha⟩

theorem rho_eq_zero {B : Subalgebra ℤ A} (x : O A B) (hx : x ∈ maximalIdeal (O A B)) : ρ A B x = 0 := by
  simp only [ρ, RingHom.comp_apply, (residue_eq_zero_iff x).2 hx, map_zero]

theorem isLocalHom_trans {B B' : Subalgebra ℤ A} (h : B ≤ B') : IsLocalHom (trans h) :=
  isLocalHom_of_le _ fun x hx => by
    rw [← residue_eq_zero_iff]
    apply (σ A B').injective
    rw [map_zero]
    change ρ A B' (trans h x) = 0
    rw [trans_rho, rho_eq_zero x hx]

theorem isLocalHom_g (B : Subalgebra ℤ A) : IsLocalHom (g A B) :=
  isLocalHom_of_le _ fun x hx => by
    rw [← residue_eq_zero_iff, g_res, rho_eq_zero x hx]

def fromB (B : Subalgebra ℤ A) : B →+* O A B := (algebraMap (RB A B) (O A B)).comp (algebraMap B (RB A B))

theorem indEt_fromB (B : Subalgebra ℤ A) : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (fromB B) := by
  letI : Algebra B (O A B) := (fromB B).toAlgebra
  haveI : IsScalarTower B (RB A B) (O A B) := IsScalarTower.of_algebraMap_eq' rfl
  have h1 : Pieces B (RB A B) := ⟨Unit, inferInstance, inferInstance, inferInstance, fun _ => ⊤,
    fun _ _ _ => le_rfl, fun _ => ⟨(), Algebra.mem_top⟩,
    fun _ => ⟨B, inferInstance, inferInstance, inferInstance, pB A B, inferInstance, ⟨Subalgebra.topEquiv.symm⟩⟩⟩
  obtain ⟨ι, _, _, _, Si, hm, hc, hl⟩ := GlobalTheory.indEtale_localPieces_trans B (RB A B) (O A B) h1 (sh A B).pieces
  exact GlobalTheory.StrictHensUnion.indEtale_of_directed_union B (O A B) ι Si hm hc (fun i => by
    obtain ⟨E, _, _, _, q, _, ⟨e⟩⟩ := hl i
    exact GlobalTheory.StrictHensUnion.indEtale_of_algEquiv e
      (GlobalTheory.StrictHensUnion.indEtale_localization_of_etale B E q.primeCompl))

theorem isStalk_O (B : Subalgebra ℤ A) :
    IsStalk (O A B) (Spec.map (CommRingCat.ofHom (fromB B))) := by
  letI : Algebra B (O A B) := (fromB B).toAlgebra
  exact ⟨⟨inferInstance, (sh A B).sep⟩, B, inferInstance, inferInstance, 𝟙 _, inferInstance, indEt_fromB B,
    (Category.comp_id _).symm⟩

variable (A) in

abbrev Idx (u : A) : Type := {B : Subalgebra ℤ A // B.FG ∧ u ∈ B}

instance (u : A) : IsDirected (Idx A u) (· ≤ ·) :=
  ⟨fun a b => ⟨⟨a.1 ⊔ b.1, a.2.1.sup b.2.1, Algebra.mem_sup_left a.2.2⟩, le_sup_left (a := a.1), le_sup_right (a := a.1)⟩⟩

def gen (u : A) (F : Finset A) : Idx A u := by
  classical
  exact ⟨Algebra.adjoin ℤ ((insert u F : Finset A) : Set A), Subalgebra.fg_adjoin_finset _,
    Algebra.subset_adjoin (by simp)⟩

theorem subset_gen (u : A) (F : Finset A) : (F : Set A) ⊆ (gen u F).1 := by
  classical
  intro x hx
  exact Algebra.subset_adjoin (by simp [hx])

instance (u : A) : Nonempty (Idx A u) := ⟨gen u ∅⟩

def Dfun (u : A) : Idx A u ⥤ CommRingCat.{0} where
  obj B := CommRingCat.of (O A B.1)
  map f := CommRingCat.ofHom (trans (leOfHom f))
  map_id B := by
    ext x
    exact DFunLike.congr_fun (trans_refl B.1) x
  map_comp f f' := by
    ext x
    exact DFunLike.congr_fun (trans_trans (leOfHom f) (leOfHom f')) x

def ιcoc (u : A) : Dfun u ⟶ (Functor.const (Idx A u)).obj (CommRingCat.of A) where
  app B := CommRingCat.ofHom (g A B.1)
  naturality B B' f := by
    ext x
    exact g_trans (leOfHom f) x

def upper (u : A) (i j : Idx A u) (F : Finset A) : Idx A u :=
  ⟨(i.1 ⊔ j.1) ⊔ (gen u F).1, (i.2.1.sup j.2.1).sup (gen u F).2.1,
    Algebra.mem_sup_left (Algebra.mem_sup_left i.2.2)⟩

def isColimit (u : A) : IsColimit (Cocone.mk _ (ιcoc u)) := by
  haveI : ReflectsColimitsOfShape (Idx A u) (forget CommRingCat.{0}) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  refine isColimitOfReflects (forget CommRingCat.{0})
    (Types.FilteredColimit.isColimitOf _ ((forget CommRingCat.{0}).mapCocone (Cocone.mk _ (ιcoc u))) ?_ ?_)
  · intro (x : A)
    classical
    let B := gen u {x}
    have hx : x ∈ B.1 := subset_gen u {x} (by simp)
    refine ⟨B, (fromB B.1 ⟨x, hx⟩ : O A B.1), ?_⟩
    change x = g A B.1 (algebraMap _ _ (algebraMap B.1 (RB A B.1) ⟨x, hx⟩))
    rw [g_alg, toA_algebraMap]
  · intro i j (xi : O A i.1) (xj : O A j.1) h
    change g A i.1 xi = g A j.1 xj at h
    have hi : i.1 ≤ i.1 ⊔ j.1 := le_sup_left
    have hj : j.1 ≤ i.1 ⊔ j.1 := le_sup_right
    have h0 : g A (i.1 ⊔ j.1) (trans hi xi - trans hj xj) = 0 := by
      rw [map_sub, g_trans hi xi, g_trans hj xj, h, sub_self]
    obtain ⟨F, hF⟩ := ker (B := i.1 ⊔ j.1) _ h0
    let k := upper u i j F
    have hk : i.1 ⊔ j.1 ≤ k.1 := le_sup_left
    have hz := hF k.1 hk (fun y hy => Algebra.mem_sup_right (subset_gen u F hy))
    rw [map_sub, sub_eq_zero] at hz
    refine ⟨k, homOfLE (hi.trans hk), homOfLE (hj.trans hk), ?_⟩
    change trans (hi.trans hk) xi = trans (hj.trans hk) xj
    rw [trans_trans hi hk, trans_trans hj hk]
    exact hz

end

theorem strictlyHenselian_isColimit : ∀ (q : ℕ) (A : Type) [CommRing A] [IsLocalRing A], SH A → IsUnit (q : A) →
  ∃ (J : Type) (_ : SmallCategory J) (_ : IsFiltered J) (D : J ⥤ CommRingCat.{0})
    (ι : D ⟶ (Functor.const J).obj (CommRingCat.of A)) (_ : IsColimit (Cocone.mk _ ι))
    (hl : ∀ j, IsLocalRing (D.obj j)),
    (∀ j, ∃ (B : Type) (_ : CommRing B) (_ : Algebra.FiniteType ℤ B)
      (s : Spec (CommRingCat.of (D.obj j)) ⟶ Spec (CommRingCat.of B)), IsStalk (D.obj j) s) ∧
    (∀ j, IsUnit (q : D.obj j)) ∧ (∀ {j k : J} (f : j ⟶ k), IsLocalHom (D.map f).hom) ∧
    ∀ j, IsLocalHom (ι.app j).hom := by
  intro q A _ _ hSH hq
  obtain ⟨hH, hsep⟩ := hSH
  let u : A := ↑hq.unit⁻¹
  refine ⟨Idx A u, inferInstance, inferInstance, Dfun u, ιcoc u, isColimit u, fun j => (inferInstance : IsLocalRing (O A j.1)),
    fun j => ?_, fun j => ?_, fun f => isLocalHom_trans (leOfHom f), fun j => isLocalHom_g j.1⟩
  · exact ⟨j.1, inferInstance, (Subalgebra.fg_iff_finiteType _).1 j.2.1, _, isStalk_O j.1⟩
  · have hqB : IsUnit ((q : ℕ) : j.1) :=
      isUnit_iff_exists_inv.2 ⟨⟨u, j.2.2⟩, Subtype.ext (by simp [u])⟩
    show IsUnit ((q : ℕ) : O A j.1)
    rw [← map_natCast (fromB j.1) q]
    exact hqB.map _

end GlobalTheory.SHColim
