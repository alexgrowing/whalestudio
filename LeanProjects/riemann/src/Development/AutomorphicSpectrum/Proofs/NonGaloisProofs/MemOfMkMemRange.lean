import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.ChainRows
import Development.AutomorphicSpectrum.Definitions.NonGaloisLines.TopLine
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.CupFlipContinuousCocycleStatement
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module GlobalTheory.CompanionTheory.LocDual

namespace GlobalTheory.CompanionTheory.LocDual.ExactAnn

section Lin

variable {k : Type*} [Field k]

theorem mem_of_orth {X Y : Type*} [AddCommGroup X] [Module k X] [AddCommGroup Y] [Module k Y]
    [FiniteDimensional k X] [FiniteDimensional k Y] (Φ : X →ₗ[k] Y →ₗ[k] k)
    (hL : ∀ x, (∀ y, Φ x y = 0) → x = 0) (hR : ∀ y, (∀ x, Φ x y = 0) → y = 0)
    (Sx : Submodule k X) (Sy : Submodule k Y) (horth : ∀ x ∈ Sx, ∀ y ∈ Sy, Φ x y = 0)
    (hdim : finrank k X ≤ finrank k Sx + finrank k Sy) (x : X) (hx : ∀ y ∈ Sy, Φ x y = 0) :
    x ∈ Sx := by
  have hinj' : Function.Injective Φ.flip := by
    intro a b hab
    refine sub_eq_zero.1 (hR (a - b) fun z => ?_)
    have e := LinearMap.congr_fun hab z
    simp only [LinearMap.flip_apply] at e
    rw [map_sub, e, sub_self]
  have hYX : finrank k Y ≤ finrank k X := by
    have := LinearMap.finrank_le_finrank_of_injective
      (f := (Φ.flip : Y →ₗ[k] Module.Dual k X)) hinj'
    rwa [Subspace.dual_finrank_eq] at this
  have hinj : Function.Injective (Φ : X →ₗ[k] Module.Dual k Y) := by
    intro a b hab
    refine sub_eq_zero.1 (hL (a - b) fun z => ?_)
    rw [map_sub, LinearMap.sub_apply, hab, sub_self]
  have hW : finrank k Sy + finrank k Sy.dualAnnihilator = finrank k Y :=
    Subspace.finrank_add_finrank_dualAnnihilator_eq Sy
  have hT : finrank k (Sy.dualAnnihilator.comap (Φ : X →ₗ[k] Module.Dual k Y)) ≤
      finrank k Sy.dualAnnihilator := by
    rw [LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj _)]
    exact Submodule.finrank_mono (Submodule.map_comap_le _ _)
  have hle : Sx ≤ Sy.dualAnnihilator.comap (Φ : X →ₗ[k] Module.Dual k Y) := by
    intro s hs
    rw [Submodule.mem_comap, Submodule.mem_dualAnnihilator]
    exact fun y hy => horth s hs y hy
  have heq := Submodule.eq_of_le_of_finrank_le hle (by omega)
  rw [heq, Submodule.mem_comap, Submodule.mem_dualAnnihilator]
  exact hx

variable {E : Type*} [AddCommGroup E] [Module k E]

def qIncl (B : Submodule k E) {S Z : Submodule k E} (h : S ≤ Z) :
    (↥S ⧸ B.comap S.subtype) →ₗ[k] (↥Z ⧸ B.comap Z.subtype) :=
  Submodule.mapQ _ _ (Submodule.inclusion h) (fun _ hx => hx)

private theorem qIncl_quotient_mk_eq_mk_inclusion (B : Submodule k E) {S Z : Submodule k E} (h : S ≤ Z) (a : ↥S) :
    qIncl B h (Submodule.Quotient.mk a) = Submodule.Quotient.mk (Submodule.inclusion h a) := by
  rfl

theorem qIncl_injective (B : Submodule k E) {S Z : Submodule k E} (h : S ≤ Z) :
    Function.Injective (qIncl B h) := by
  intro a b hab
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  simp only [qIncl_quotient_mk_eq_mk_inclusion] at hab
  rw [Submodule.Quotient.eq] at hab ⊢
  rw [Submodule.mem_comap] at hab ⊢
  simpa using hab

theorem mem_of_mk_mem_range {B S Z : Submodule k E} (hBS : B ≤ S) (h : S ≤ Z) (a : ↥Z)
    (ha : (Submodule.Quotient.mk a : ↥Z ⧸ B.comap Z.subtype) ∈ LinearMap.range (qIncl B h)) :
    (a : E) ∈ S := by
  obtain ⟨q, hq⟩ := LinearMap.mem_range.1 ha
  obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  simp only [qIncl_quotient_mk_eq_mk_inclusion] at hq
  rw [Submodule.Quotient.eq, Submodule.mem_comap] at hq
  have h1 : ((s : E) - a) ∈ S := hBS (by simpa using hq)
  have h2 := sub_mem s.2 h1
  simpa using h2

variable {E' : Type*} [AddCommGroup E'] [Module k E']

theorem ann_of_pairing (Z B S : Submodule k E) (Z' B' S' : Submodule k E')
    (Φ : ↥Z →ₗ[k] ↥Z' →ₗ[k] k)
    (hBl : ∀ a : ↥Z, (a : E) ∈ B → ∀ b, Φ a b = 0) (hBr : ∀ b : ↥Z', (b : E') ∈ B' → ∀ a, Φ a b = 0)
    (hL : ∀ a : ↥Z, (∀ b, Φ a b = 0) → (a : E) ∈ B) (hR : ∀ b : ↥Z', (∀ a, Φ a b = 0) → (b : E') ∈ B')
    [FiniteDimensional k (↥Z ⧸ B.comap Z.subtype)] [FiniteDimensional k (↥Z' ⧸ B'.comap Z'.subtype)]
    (hBS : B ≤ S) (hSZ : S ≤ Z) (hBS' : B' ≤ S') (hSZ' : S' ≤ Z')
    (horth : ∀ (a : ↥Z) (b : ↥Z'), (a : E) ∈ S → (b : E') ∈ S' → Φ a b = 0)
    (hdim : finrank k (↥Z ⧸ B.comap Z.subtype) ≤ finrank k (↥S ⧸ B.comap S.subtype) +
      finrank k (↥S' ⧸ B'.comap S'.subtype)) :
    (∀ a : ↥Z, (∀ b : ↥Z', (b : E') ∈ S' → Φ a b = 0) → (a : E) ∈ S) ∧
    (∀ b : ↥Z', (∀ a : ↥Z, (a : E) ∈ S → Φ a b = 0) → (b : E') ∈ S') := by
  classical
  let Ψ1 : (↥Z' ⧸ B'.comap Z'.subtype) →ₗ[k] ↥Z →ₗ[k] k :=
    (B'.comap Z'.subtype).liftQ Φ.flip (fun b hb => by
      rw [LinearMap.mem_ker]
      ext a
      simpa using hBr b hb a)
  let Φb : (↥Z ⧸ B.comap Z.subtype) →ₗ[k] (↥Z' ⧸ B'.comap Z'.subtype) →ₗ[k] k :=
    (B.comap Z.subtype).liftQ Ψ1.flip (fun a ha => by
      rw [LinearMap.mem_ker]
      ext b
      simpa [Ψ1] using hBl a ha b)
  have hΦb : ∀ a b, Φb (Submodule.Quotient.mk a) (Submodule.Quotient.mk b) = Φ a b := by
    intro a b
    simp [Φb, Ψ1]
  have hLb : ∀ x, (∀ y, Φb x y = 0) → x = 0 := by
    intro x hx
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [Submodule.Quotient.mk_eq_zero]
    exact hL a fun b => by simpa [hΦb] using hx (Submodule.Quotient.mk b)
  have hRb : ∀ y, (∀ x, Φb x y = 0) → y = 0 := by
    intro y hy
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [Submodule.Quotient.mk_eq_zero]
    exact hR b fun a => by simpa [hΦb] using hy (Submodule.Quotient.mk a)
  have hSx : finrank k (LinearMap.range (qIncl B hSZ)) = finrank k (↥S ⧸ B.comap S.subtype) :=
    LinearMap.finrank_range_of_inj (qIncl_injective B hSZ)
  have hSy : finrank k (LinearMap.range (qIncl B' hSZ')) =
      finrank k (↥S' ⧸ B'.comap S'.subtype) :=
    LinearMap.finrank_range_of_inj (qIncl_injective B' hSZ')
  have horthb : ∀ x ∈ LinearMap.range (qIncl B hSZ), ∀ y ∈ LinearMap.range (qIncl B' hSZ'),
      Φb x y = 0 := by
    intro x hx y hy
    obtain ⟨p, rfl⟩ := LinearMap.mem_range.1 hx
    obtain ⟨q, rfl⟩ := LinearMap.mem_range.1 hy
    obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective _ p
    obtain ⟨s', rfl⟩ := Submodule.Quotient.mk_surjective _ q
    simp only [qIncl_quotient_mk_eq_mk_inclusion, hΦb]
    exact horth _ _ s.2 s'.2
  have hdimb : finrank k (↥Z ⧸ B.comap Z.subtype) ≤
      finrank k (LinearMap.range (qIncl B hSZ)) + finrank k (LinearMap.range (qIncl B' hSZ')) := by
    rw [hSx, hSy]
    exact hdim
  have hYX : finrank k (↥Z' ⧸ B'.comap Z'.subtype) ≤ finrank k (↥Z ⧸ B.comap Z.subtype) := by
    have hinj : Function.Injective
        (Φb.flip : (↥Z' ⧸ B'.comap Z'.subtype) →ₗ[k] Module.Dual k (↥Z ⧸ B.comap Z.subtype)) := by
      intro a b hab
      refine sub_eq_zero.1 (hRb (a - b) fun z => ?_)
      have e := LinearMap.congr_fun hab z
      simp only [LinearMap.flip_apply] at e
      rw [map_sub, e, sub_self]
    have := LinearMap.finrank_le_finrank_of_injective hinj
    rwa [Subspace.dual_finrank_eq] at this
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · have hmem := mem_of_orth Φb hLb hRb _ _ horthb hdimb (Submodule.Quotient.mk a) (by
      intro y hy
      obtain ⟨q, rfl⟩ := LinearMap.mem_range.1 hy
      obtain ⟨s', rfl⟩ := Submodule.Quotient.mk_surjective _ q
      simp only [qIncl_quotient_mk_eq_mk_inclusion, hΦb]
      exact ha _ s'.2)
    exact mem_of_mk_mem_range hBS hSZ a hmem
  · have hmem := mem_of_orth Φb.flip (fun y h => hRb y fun x => by simpa using h x)
      (fun x h => hLb x fun y => by simpa using h y) _ _
      (fun y hy x hx => by rw [LinearMap.flip_apply]; exact horthb x hx y hy)
      (by rw [add_comm]; exact hYX.trans hdimb) (Submodule.Quotient.mk b) (by
        intro x hx
        obtain ⟨p, rfl⟩ := LinearMap.mem_range.1 hx
        obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective _ p
        simp only [qIncl_quotient_mk_eq_mk_inclusion, LinearMap.flip_apply, hΦb]
        exact hb _ s.2)
    exact mem_of_mk_mem_range hBS' hSZ' b hmem

end Lin

section Functional

variable {k : Type*} [Field k] {E E' F : Type*} [AddCommGroup E] [Module k E] [AddCommGroup E']
  [Module k E'] [AddCommGroup F] [Module k F]

theorem exists_pairing (Z : Submodule k E) (Z' : Submodule k E') (M C : Submodule k F)
    (cup : E →ₗ[k] E' →ₗ[k] F) (hM : ∀ a ∈ Z, ∀ b ∈ Z', cup a b ∈ M) (z0 : F)
    (hz0C : z0 ∉ C) (hline : ∀ z ∈ M, ∃ a : k, z - a • z0 ∈ C) :
    ∃ Φ : ↥Z →ₗ[k] ↥Z' →ₗ[k] k, ∀ (a : ↥Z) (b : ↥Z'), Φ a b = 0 ↔ cup a b ∈ C := by
  classical
  have huniq : ∀ z : F, ∀ a a' : k, z - a • z0 ∈ C → z - a' • z0 ∈ C → a = a' := by
    intro z a a' h h'
    by_contra hne
    have hd : (a' - a) • z0 ∈ C := by
      have := C.sub_mem h h'
      rwa [show z - a • z0 - (z - a' • z0) = (a' - a) • z0 by rw [sub_smul]; abel] at this
    have hne' : a' - a ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
    apply hz0C
    have := C.smul_mem (a' - a)⁻¹ hd
    rwa [smul_smul, inv_mul_cancel₀ hne', one_smul] at this
  let g : ↥M → k := fun z => (hline z z.2).choose
  have hg : ∀ z : ↥M, (z : F) - g z • z0 ∈ C := fun z => (hline z z.2).choose_spec
  let f : ↥M →ₗ[k] k :=
    { toFun := g
      map_add' := fun z w => huniq _ _ _ (hg (z + w)) (by
        convert C.add_mem (hg z) (hg w) using 1
        rw [Submodule.coe_add, add_smul]
        abel)
      map_smul' := fun c z => by
        simp only [RingHom.id_apply, smul_eq_mul]
        refine huniq _ _ _ (hg (c • z)) ?_
        convert C.smul_mem c (hg z) using 1
        rw [Submodule.coe_smul, smul_sub, mul_smul] }
  refine ⟨LinearMap.mk₂ k (fun a b => f ⟨cup a b, hM a a.2 b b.2⟩) ?_ ?_ ?_ ?_, ?_⟩
  · intro a a' b
    rw [← map_add]
    congr 1
    ext
    simp
  · intro c a b
    rw [← map_smul]
    congr 1
    ext
    simp
  · intro a b b'
    rw [← map_add]
    congr 1
    ext
    simp
  · intro c a b
    rw [← map_smul]
    congr 1
    ext
    simp
  · intro a b
    rw [LinearMap.mk₂_apply]
    change g ⟨cup a b, hM a a.2 b b.2⟩ = 0 ↔ _
    constructor
    · intro h0
      have := hg ⟨cup a b, hM a a.2 b b.2⟩
      rwa [h0, zero_smul, sub_zero] at this
    · intro hC
      exact huniq _ _ _ (hg ⟨cup a b, hM a a.2 b b.2⟩) (by rwa [zero_smul, sub_zero])

end Functional

section Cup

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    (LL : Type) [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [IsTopologicalRing LL]

def cocSub : Submodule LL (G × G → LL) where
  carrier := {z | Continuous z ∧ ReciprocityTheory.Def.d2 (charRep (cycLL PD LL)) z = 0}
  zero_mem' := ⟨continuous_const, map_zero _⟩
  add_mem' := fun ha hb => ⟨ha.1.add hb.1, by rw [map_add, ha.2, hb.2, add_zero]⟩
  smul_mem' := fun c _ ha => ⟨ha.1.const_smul c, by rw [map_smul, ha.2, smul_zero]⟩

def cobSub : Submodule LL (G × G → LL) where
  carrier := {z | CobL PD z}
  zero_mem' := ⟨0, continuous_const, map_zero _⟩
  add_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f + g, hf.add hg, map_add _ _ _⟩
  smul_mem' := by
    rintro c _ ⟨f, hf, rfl⟩
    exact ⟨c • f, hf.const_smul c, map_smul _ _ _⟩

variable {LL} {V V' : Type} [AddCommGroup V] [Module LL V] [AddCommGroup V'] [Module LL V']

def cupBil (ρ' : Representation LL G V') (P : V →ₗ[LL] V' →ₗ[LL] LL) :
    (G → V) →ₗ[LL] (G → V') →ₗ[LL] (G × G → LL) :=
  LinearMap.mk₂ LL (cupL ρ' P)
    (fun a a' b => by ext x; simp [cupL])
    (fun r a b => by ext x; simp [cupL])
    (fun a b b' => by ext x; simp [cupL])
    (fun r a b => by ext x; simp [cupL])

theorem cupBil_apply (ρ' : Representation LL G V') (P : V →ₗ[LL] V' →ₗ[LL] LL) (a : G → V)
    (b : G → V') : cupBil ρ' P a b = cupL ρ' P a b := rfl

end Cup

end GlobalTheory.CompanionTheory.LocDual.ExactAnn
