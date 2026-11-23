import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameDualUnipotentGroupActsUnitriangularOntoStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualLatticeFrameEqStandardTranslateStatement

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical

namespace GlobalTheory.LocOver.TermOver

section

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

lemma mem_img (g : V ≃ₗ[E] V) (Λ : Submodule M.L.O V) (x : V) :
    x ∈ img g Λ ↔ ∃ y ∈ Λ, g y = x := by
  simp [img, Submodule.mem_map]

lemma img_mul (g k : V ≃ₗ[E] V) (Λ : Submodule M.L.O V) : img (g * k) Λ = img g (img k Λ) := by
  ext x
  simp only [mem_img]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨k y, ⟨y, hy, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, rfl⟩

lemma img_one (Λ : Submodule M.L.O V) : img (1 : V ≃ₗ[E] V) Λ = Λ := by
  ext x
  simp only [mem_img]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨x, hx, rfl⟩

lemma img_selfDual (H : HermSp M V) {g : V ≃ₗ[E] V} (hg : IsUnitary H g)
    {Λ : Submodule M.L.O V} (hΛ : H.IsSelfDual Λ) : H.IsSelfDual (img g Λ) := by
  obtain ⟨h1, h2, h3⟩ := hΛ
  refine ⟨h1.map _, ?_, ?_⟩
  · have himg : ((img g Λ : Submodule M.L.O V) : Set V) = (g : V →ₗ[E] V) '' (Λ : Set V) := by
      ext x
      simp only [SetLike.mem_coe, mem_img, Set.mem_image]
      rfl
    rw [himg, ← Submodule.map_span, h2, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr g.surjective
  · intro x
    constructor
    · intro hx y hy
      obtain ⟨a, ha, rfl⟩ := (mem_img g Λ x).1 hx
      obtain ⟨b, hb, rfl⟩ := (mem_img g Λ y).1 hy
      rw [hg]
      exact (h3 a).1 ha b hb
    · intro hx
      obtain ⟨a, rfl⟩ := g.surjective x
      refine (mem_img g Λ _).2 ⟨a, (h3 a).2 fun y hy => ?_, rfl⟩
      have := hx (g y) ((mem_img g Λ _).2 ⟨y, hy, rfl⟩)
      rwa [hg] at this

lemma img_frame (H : HermSp M V) {g : V ≃ₗ[E] V} (hg : IsUnitary H g)
    {Λ : Submodule M.L.O V} {r : ℕ} {f : Fin (r + 1) → V} {T : F} (hf : H.IsFrame Λ r f T) :
    H.IsFrame (img g Λ) r (fun b => g (f b)) T := by
  obtain ⟨⟨p1, p2, p3⟩, h2, h3, h4, h5⟩ := hf
  refine ⟨⟨fun a => (mem_img g Λ _).2 ⟨f a, p1 a, rfl⟩, ?_, ?_⟩, ?_, ?_, h4, h5⟩
  · exact p2.map' (g : V →ₗ[E] V) (LinearEquiv.ker g)
  · intro x hx hs
    obtain ⟨y, hy, rfl⟩ := (mem_img g Λ x).1 hx
    have hrange : Set.range (fun b => g (f b)) = (g : V →ₗ[E] V) '' Set.range f := by
      rw [← Set.range_comp]
      rfl
    rw [hrange, ← Submodule.map_span] at hs
    obtain ⟨y', hy', hyy⟩ := hs
    have hyy' : y' = y := g.injective hyy
    subst hyy'
    have hO := p3 y' hy hy'
    have hmap : ∀ v ∈ Submodule.span M.L.O (Set.range f),
        g v ∈ Submodule.span M.L.O (Set.range fun b => g (f b)) := by
      intro v hv
      induction hv using Submodule.span_induction with
      | mem v hv =>
        obtain ⟨b, rfl⟩ := hv
        exact Submodule.subset_span ⟨b, rfl⟩
      | zero => simp
      | add a b _ _ ha hb =>
        rw [map_add]
        exact Submodule.add_mem _ ha hb
      | smul c a _ ha =>
        have : g (c • a) = c • g a := by
          change g ((c : E) • a) = (c : E) • g a
          exact map_smul g (c : E) a
        rw [this]
        exact Submodule.smul_mem _ c ha
    exact hmap y' hO
  · intro a b hab
    rw [hg]
    exact h2 a b hab
  · rw [hg]
    exact h3

lemma side (hM : M.OK) (H : HermSp M V) (r : ℕ) (Fr : FrameD H r) {Λ : Submodule M.L.O V}
    {f : Fin (r + 1) → V} (hΛ : H.IsSelfDual Λ) (hf : H.IsFrame Λ r f Fr.T) (hT : Tri E Fr.f f) :
    ∃ L : Submodule M.L.O (H.Wb Fr.f), Fr.IsInner L ∧
      ∃ n ∈ Fr.N, f = (fun b => n (Fr.f b)) ∧ Λ = img n (Fr.LamStd L) := by
  obtain ⟨h1, -, h3⟩ := GlobalTheory.T.frameDual_unipotentGroup_acts_unitriangular_onto M hM H r Fr hf.2.2.2.2
  obtain ⟨n, hn, hnf⟩ := h3 f hT
  have hu : IsUnitary H n⁻¹ := ((h1 _).1 (Fr.N.inv_mem hn)).1
  have hfr : H.IsFrame (img n⁻¹ Λ) r Fr.f Fr.T := by
    have := img_frame H hu hf
    have he : (fun b => n⁻¹ (f b)) = Fr.f := by
      funext b
      rw [hnf]
      exact n.symm_apply_apply _
    rwa [he] at this
  obtain ⟨L, hL, -, n0, hn0, hfix, hΛ0⟩ :=
    GlobalTheory.T.selfDual_lattice_frame_eq_standard_translate M hM H r Fr (img n⁻¹ Λ) (img_selfDual H hu hΛ) hfr
  refine ⟨L, hL, n * n0, Fr.N.mul_mem hn hn0, ?_, ?_⟩
  · rw [hnf]
    funext b
    change n (Fr.f b) = n (n0 (Fr.f b))
    rw [hfix]
  · rw [img_mul, ← hΛ0, ← img_mul, mul_inv_cancel, img_one]

end

theorem exists_datum : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ), ∀ (P : FPair H r) (t : Term V M r), H.IsTerm t → t.T = P.A.T → t.T' = P.B.T → Tri E P.A.f t.f → Tri E P.B.f t.f' → ∃ d : Datum P, IsTermOver P d t := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r P t ht hT hT' hf hf'
  obtain ⟨hsd, hfr, hfr', -, -, hg⟩ := ht
  rw [hT] at hfr
  rw [hT'] at hfr'
  obtain ⟨L, hL, n, hn, hnf, hnΛ⟩ := side hM H r P.A hsd hfr hf
  obtain ⟨L', hL', n', hn', hnf', hnΛ'⟩ := side hM H r P.B hsd hfr' hf'
  let s : Term V M r := ⟨t.abelian₂, P.A.f, P.B.f, t.T, t.T'⟩
  refine ⟨⟨L, L', hL, hL', {p | ∃ g, M.split = some g ∧ p ∈ H.iotaGraph g s}, ?_⟩, hT, hT',
    ⟨n, hn, hnf, hnΛ⟩, ⟨n', hn', hnf', hnΛ'⟩, ?_⟩
  · intro h
    ext p
    simp [h]
  · intro g hgs
    refine ⟨(hg g hgs).2.2, ?_⟩
    ext p
    constructor
    · intro hp
      exact ⟨g, hgs, hp⟩
    · rintro ⟨g', hg', hp⟩
      obtain rfl : g = g' := Option.some.inj (hgs.symm.trans hg')
      exact hp

end GlobalTheory.LocOver.TermOver
