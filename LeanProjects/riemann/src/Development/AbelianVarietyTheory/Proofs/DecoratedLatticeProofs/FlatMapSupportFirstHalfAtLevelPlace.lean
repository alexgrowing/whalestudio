import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.AllPositions
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBesselStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapsPreserveSchwartzBruhatAndSurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.StepData GlobalTheory.SymChain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocMod.SuppFirst

theorem e_mul_ι {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) (x : k) : p.e * p.ι x = p.ι x := by
  rw [← p.ι_π, p.π_ι]

theorem ι_mul' {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) (x y : k) : p.ι (x * y) = p.ι x * p.ι y := by
  have h := p.ι_π (p.ι x * p.ι y)
  rw [map_mul, p.π_ι, p.π_ι, ← mul_assoc, e_mul_ι] at h
  exact h

theorem ι_one' {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) : p.ι 1 = p.e := by
  have h := p.ι_π 1
  rwa [map_one, mul_one] at h

theorem shift_mul {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) (x y : k) :
    (p.ι x + (1 - p.e)) * (p.ι y + (1 - p.e)) = p.ι (x * y) + (1 - p.e) := by
  have he : p.e * p.e = p.e := p.split.1
  have h1 : p.ι x * (1 - p.e) = 0 := by
    rw [mul_sub, mul_one, mul_comm, e_mul_ι, sub_self]
  have h2 : (1 - p.e) * p.ι y = 0 := by
    rw [sub_mul, one_mul, e_mul_ι, sub_self]
  have h3 : (1 - p.e) * (1 - p.e) = 1 - p.e := by
    rw [sub_mul, one_mul, mul_sub, mul_one, he, sub_self, sub_zero]
  rw [ι_mul', add_mul, mul_add, mul_add, h1, h2, h3, add_zero, zero_add]

def shiftU {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) : kˣ →* (AE D)ˣ where
  toFun x := ⟨p.ι x + (1 - p.e), p.ι (x⁻¹ : kˣ) + (1 - p.e), by
      rw [shift_mul, Units.mul_inv, ι_one']; ring, by
      rw [shift_mul, Units.inv_mul, ι_one']; ring⟩
  map_one' := by ext; simp [ι_one']
  map_mul' x y := by ext; simp [shift_mul]

theorem exists_comp {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) (χ : (AE D)ˣ →* Circle) : ∃ μ : kˣ →* ℂˣ, p.IsComp χ μ := by
  refine ⟨Circle.toUnits.comp (χ.comp (shiftU p)), fun x a ha => ?_⟩
  have : shiftU p x = a := Units.ext ha.symm
  simp [this]

theorem card_frame {k : Type} [Field k] {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y] (Fr : Frame k N Y) :
    Fintype.card Y = N := by
  apply le_antisymm
  · have h := Matrix.rank_mul_le_left Fr.γ Fr.β
    rw [Fr.γβ, Matrix.rank_one] at h
    have h' := Matrix.rank_le_card_width Fr.γ
    rw [Fintype.card_fin] at h'
    exact h.trans h'
  · have h := Matrix.rank_mul_le_left Fr.β Fr.γ
    rw [Fr.βγ, Matrix.rank_one, Fintype.card_fin] at h
    exact h.trans (Matrix.rank_le_card_width Fr.β)

def prH {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) : D.host.E →+* k := p.π.comp (incA D)

theorem prH_apply {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) (a : D.host.E) : prH p a = p.pr a := rfl

theorem exists_coreFrame {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) {σ : ℕ} {B : BesLev D (σ + 1)} {J : JacLev D (σ + 1)} {B' : BesLev D σ} {n₀ n₁ n₂ : Type}
    [Fintype n₀] [DecidableEq n₀] [Fintype n₁] [DecidableEq n₁] [Fintype n₂] [DecidableEq n₂] {c : ℕ}
    (F : Dbl p B J B' n₀ n₁ n₂ c) : ∃ C : Frame k B.V₀.rank (n₀ ⊕ Unit), p.IsCoreFrame B F.s F.F₀ C := by
  obtain ⟨hc, hA, -, hz, -⟩ := F.bes
  let M : Matrix (Fin B.V₀.rank) (n₀ ⊕ Unit) k :=
    fromCols (B.o.iA.map p.pr * F.F₀.β) (Matrix.of fun r (_ : Unit) => F.s * p.pr (vecB B.o B.ζ r))
  let f : n₀ ⊕ Unit → n₀ ⊕ Fin (c + 1 + 1 + 1) := Sum.elim Sum.inl fun _ => Sum.inr ⟨σ + 1, by omega⟩
  have hf : Function.Injective f := by
    rintro (a | _) (b | _) h <;> simp_all [f]
  have key : B.d.i₀.map p.pr * M = F.G₀.β.submatrix id f := by
    ext r (a | _)
    · simp only [M, f, Matrix.mul_fromCols, fromCols_apply_inl, submatrix_apply, id, Sum.elim_inl]
      rw [hA r a, ← Matrix.mul_assoc]
      have hm : B.d.i₀.map p.pr * B.o.iA.map p.pr = (B.d.i₀ * B.o.iA).map p.pr :=
        (Matrix.map_mul (f := prH p)).symm
      rw [hm]
    · simp only [M, f, Matrix.mul_fromCols, fromCols_apply_inr, submatrix_apply, id, Sum.elim_inr]
      rw [hz ⟨σ + 1, by omega⟩ rfl r]
      simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.map_apply, mulVec, dotProduct]
      rw [← prH_apply, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [map_mul, prH_apply, prH_apply]
      ring
  let L : Matrix (n₀ ⊕ Unit) (Fin B.V₀.rank) k := F.G₀.γ.submatrix f id * B.d.i₀.map p.pr
  have hLM : L * M = 1 := by
    simp only [L, Matrix.mul_assoc, key]
    rw [← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, F.G₀.γβ]
    exact Matrix.submatrix_one _ hf
  have hcard : Fintype.card (n₀ ⊕ Unit) = B.V₀.rank := by
    have h1 := card_frame F.G₀
    have h2 := B.d.rank_add
    simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit] at h1 ⊢
    omega
  have hML : M * L = 1 :=
    (Matrix.mul_eq_one_comm_of_card_eq (n₀ ⊕ Unit) (Fin B.V₀.rank) k (A := L) (B := M) (by simpa using hcard)).mp hLM
  refine ⟨⟨M, L, hML, hLM⟩, fun r a => ?_, fun r => ?_⟩
  · simp [M]
  · simp [M]

theorem isLoc_one {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) {V : HSp D} {Y : Type} [Fintype Y] [DecidableEq Y] (Fr : Frame k V.rank Y) : p.IsLoc Fr 1 1 := by
  obtain ⟨hloc, -, -⟩ := GlobalTheory.T.splitPlace_localGroupElements_jacobi_bessel D k p
  obtain ⟨g₀, hg₀, hu⟩ := (hloc V Y Fr).1 1
  have h2 := (hloc V Y Fr).2.2 _ _ _ _ hg₀ hg₀
  rw [mul_one] at h2
  have e : g₀ * g₀ = g₀ := hu _ h2
  have : g₀ = 1 := by
    have := congrArg (g₀⁻¹ * ·) e
    simpa [← mul_assoc] using this
  exact this ▸ hg₀

theorem gsupp1 : ∀ (D : D7), OmLoc D → FlatBF D → GlobalTheory.LocFlat.SymCollapse → GSupp1 D := by
  intro D hOm hFl hSym k _ _ _ _ p s κ S t _ _ ψ hψ j c H σ B J B' F s₁ hμ T₁ hT₁ Φ₁ hΦ₁ h hh hne
  obtain ⟨hloc, hjac, -⟩ := GlobalTheory.T.splitPlace_localGroupElements_jacobi_bessel D k p
  letI : MeasurableSpace k := borel k
  haveI : BorelSpace k := ⟨rfl⟩
  obtain ⟨ν, hν⟩ := exists_isUnitVol k
  haveI := hν.1
  obtain ⟨hk, hhk⟩ := (hloc J.W _ F.G₁).2.1 h hh
  have hc : c = 2 * σ := by have := F.bes.1; omega

  obtain ⟨μT, hT⟩ := exists_comp p s₁.χW
  have hS : p.IsComp s₁.χV (S.μ (j + 1))⁻¹ := by
    intro x a ha
    have := hμ x a ha
    simp only [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, Circle.coe_inv] at this ⊢
    rw [this, inv_inv]

  let Φ' : SB (Matrix (XIx (Fin κ) t (j + 1) ⊕ Fin (c + 1 + 1)) (XIx (Fin κ) t j ⊕ Fin (c + 1 + 1 + 1)) k) :=
    ⟨om (S.μ (j + 1)) 1 hk Φ₁.1, om_mem_SB (μ := S.μ (j + 1)) (1 : GL _ k) hk Φ₁.2⟩
  have hom : s₁.om (1, h) (T₁ Φ₁) = T₁ Φ' := by
    refine hOm k p ψ B.V J.W s₁.χV s₁.χW s₁.om s₁.weil _ μT hS hT _ _ F.G₀ F.G₁ T₁ hT₁ 1 1 h hk
      (isLoc_one p _) hhk Φ₁ Φ' ?_
    simp [Φ']

  obtain ⟨C, hC⟩ := exists_coreFrame p F
  obtain ⟨T₀, -, hT₀⟩ := hFl k p ν hν.1 ψ S.ψ hψ (σ + 1) B J s₁ F.s F.s_ne _ _ (c + 1 + 1) F.F₀ C F.G₀ F.F₁ F.G₁
    hC F.bes F.jac T₁ hT₁
  have hSB := ((GlobalTheory.T.flatMaps_preserve_schwartzBruhat_and_surjective k S.ψ ν S.cond.continuous hν.1 _ _ (c + 1 + 1) (σ + 1 + 1) (by omega)).1
    (by omega)).1 Φ'.1 Φ'.2
  have hflat := hT₀ Φ' ⟨_, hSB⟩ rfl
  rw [hom, hflat] at hne
  have hne' : GlobalTheory.LocFlat.flCol S.ψ ν (σ + 1 + 1) (om (S.μ (j + 1)) 1 hk ((S.T t).Phi j (c + 1 + 1) (by omega))) ≠ 0 := by
    intro h0
    apply hne
    have : (⟨_, hSB⟩ : SB _) = 0 := by
      ext1
      simpa [Φ', hΦ₁] using h0
    rw [this, map_zero]
  obtain ⟨β, q, hq, u, hu, hkeq⟩ := (hSym k ν hν s κ S t).1 j (c + 1) (by omega) (σ + 1) (by omega) hk hne'
  obtain ⟨r, hr, -⟩ := (hloc J.W _ F.G₁).1 (colE (c + 1 + 1) (σ + 1 + 1) β * q)
  obtain ⟨u', hu', -⟩ := (hloc J.W _ F.G₁).1 u
  have hprod := (hloc J.W _ F.G₁).2.2 _ _ _ _ hr hu'
  rw [← hkeq] at hprod
  obtain ⟨g', -, huniq⟩ := (hloc J.W _ F.G₁).1 hk
  refine ⟨r, hjac _ _ _ _ _ _ _ _ F.jac r β q hq hr, hr.1, u', u, hu', hu, ?_⟩
  exact (huniq _ hhk).trans (huniq _ hprod).symm

end GlobalTheory.LocMod.SuppFirst
