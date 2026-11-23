import Mathlib
import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Classical

noncomputable section

namespace GlobalTheory.TieLat

section Gen

variable {E E' : Type} [Field E] [NumberField E] [StarRing E] [Field E'] [NumberField E'] [StarRing E']

def cw (i : E ≃+* E') {n : ℕ} (x : Sp E n) : Fin n → E' := fun k => i (x k)

def cwInv (i : E ≃+* E') {n : ℕ} (y : Fin n → E') : Sp E n := fun k => i.symm (y k)

theorem cw_cwInv (i : E ≃+* E') {n : ℕ} (y : Fin n → E') : cw i (cwInv i y) = y := by
  funext k; simp [cw, cwInv]

theorem cwInv_cw (i : E ≃+* E') {n : ℕ} (x : Sp E n) : cwInv i (cw i x) = x := by
  funext k; simp [cw, cwInv]

theorem coe_iO_symm (i : E ≃+* E') (r : 𝓞 E') :
    (((RingOfIntegers.mapRingEquiv i).symm r : 𝓞 E) : E) = i.symm (r : E') := rfl

theorem cwInv_smul (i : E ≃+* E') {n : ℕ} (r : 𝓞 E') (y : Fin n → E') :
    cwInv i (r • y) = (RingOfIntegers.mapRingEquiv i).symm r • cwInv i y := by
  funext k
  simp only [cwInv, Pi.smul_apply]
  rw [Algebra.smul_def, Algebra.smul_def, map_mul]
  rfl

theorem mem_span_cw (i : E ≃+* E') {n : ℕ} (N : Submodule (𝓞 E) (Sp E n)) (y : Fin n → E') :
    y ∈ Submodule.span (𝓞 E') ((fun (x : Sp E n) (k : Fin n) => i (x k)) '' (N : Set (Sp E n))) ↔ cwInv i y ∈ N := by
  constructor
  · intro h
    induction h using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨x, hx, rfl⟩ := hy
      have : cwInv i (fun k => i (x k)) = x := cwInv_cw i x
      rw [this]; exact hx
    | zero =>
      have : cwInv i (0 : Fin n → E') = 0 := by funext k; simp [cwInv]
      rw [this]; exact N.zero_mem
    | add a b _ _ ha hb =>
      have : cwInv i (a + b) = cwInv i a + cwInv i b := by funext k; simp [cwInv]
      rw [this]; exact N.add_mem ha hb
    | smul r a _ ha =>
      rw [cwInv_smul]; exact N.smul_mem _ ha
  · intro h
    exact Submodule.subset_span ⟨cwInv i y, h, cw_cwInv i y⟩

theorem isSdLat_of_transport (i : E ≃+* E') (hst : ∀ x, i (star x) = star (i x)) {n : ℕ} (N : Submodule (𝓞 E) (Sp E n))
    (h : IsSDLat E' n (Submodule.span (𝓞 E') ((fun (x : Sp E n) (k : Fin n) => i (x k)) '' (N : Set (Sp E n))))) :
    IsSdLat N := by
  set L := Submodule.span (𝓞 E') ((fun (x : Sp E n) (k : Fin n) => i (x k)) '' (N : Set (Sp E n))) with hL
  have hmem : ∀ y, y ∈ L ↔ cwInv i y ∈ N := mem_span_cw i N
  have hmem' : ∀ x, cw i x ∈ L ↔ x ∈ N := fun x => by rw [hmem, cwInv_cw]
  obtain ⟨hfg, hspan, hdual⟩ := h
  refine ⟨⟨?_, ?_⟩, ?_⟩
  ·
    obtain ⟨S, hS⟩ := hfg
    refine ⟨S.image (cwInv i), ?_⟩
    apply le_antisymm
    · rw [Submodule.span_le]
      intro x hx
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx
      obtain ⟨s, hs, rfl⟩ := hx
      have : s ∈ L := hS ▸ Submodule.subset_span hs
      exact (hmem s).1 this
    · intro x hx
      have hy : cw i x ∈ Submodule.span (𝓞 E') (S : Set (Fin n → E')) := hS ▸ (hmem' x).2 hx
      have key : ∀ y ∈ Submodule.span (𝓞 E') (S : Set (Fin n → E')),
          cwInv i y ∈ Submodule.span (𝓞 E) ((S.image (cwInv i) : Finset (Sp E n)) : Set (Sp E n)) := by
        intro y hy
        induction hy using Submodule.span_induction with
        | mem y hy => exact Submodule.subset_span (by simpa using ⟨y, hy, rfl⟩)
        | zero =>
          have : cwInv i (0 : Fin n → E') = 0 := by funext k; simp [cwInv]
          rw [this]; exact Submodule.zero_mem _
        | add a b _ _ ha hb =>
          have : cwInv i (a + b) = cwInv i a + cwInv i b := by funext k; simp [cwInv]
          rw [this]; exact Submodule.add_mem _ ha hb
        | smul r a _ ha =>
          rw [cwInv_smul]; exact Submodule.smul_mem _ _ ha
      have := key _ hy
      rwa [cwInv_cw] at this
  ·
    rw [eq_top_iff]
    intro x _
    have hy : cw i x ∈ Submodule.span E' (L : Set (Fin n → E')) := hspan ▸ Submodule.mem_top
    have key : ∀ y ∈ Submodule.span E' (L : Set (Fin n → E')),
        cwInv i y ∈ Submodule.span E (N : Set (Sp E n)) := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy => exact Submodule.subset_span ((hmem y).1 hy)
      | zero =>
        have : cwInv i (0 : Fin n → E') = 0 := by funext k; simp [cwInv]
        rw [this]; exact Submodule.zero_mem _
      | add a b _ _ ha hb =>
        have : cwInv i (a + b) = cwInv i a + cwInv i b := by funext k; simp [cwInv]
        rw [this]; exact Submodule.add_mem _ ha hb
      | smul r a _ ha =>
        have : cwInv i (r • a) = i.symm r • cwInv i a := by
          funext k; simp [cwInv]
        rw [this]; exact Submodule.smul_mem _ _ ha
    have := key _ hy
    rwa [cwInv_cw] at this
  ·
    have hform : ∀ x y : Sp E n, stdH E' n (cw i x) (cw i y) = i (hStd E n x y) := by
      intro x y
      simp only [stdH, cw, hStd, LinearMap.mk₂'ₛₗ_apply, map_sum, map_mul, hst]
    have hrange : ∀ w : E, i w ∈ (algebraMap (𝓞 E') E').range ↔ w ∈ (1 : Submodule (𝓞 E) E) := by
      intro w
      rw [Submodule.mem_one]
      constructor
      · rintro ⟨r, hr⟩
        refine ⟨(RingOfIntegers.mapRingEquiv i).symm r, ?_⟩
        have : i.symm (r : E') = w := by
          have h2 : (r : E') = i w := hr
          rw [h2]; simp
        exact this
      · rintro ⟨r, rfl⟩
        exact ⟨RingOfIntegers.mapRingEquiv i r, rfl⟩
    unfold IsUnimodular dual Formalism.E.hdual
    ext y
    simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.coe_restrictScalars]
    rw [← hmem' y, hdual (cw i y)]
    constructor
    · intro hy x' hx'
      have h1 := hy (cwInv i x') ((hmem x').1 hx')
      rw [← cw_cwInv i x', hform]
      exact (hrange _).2 h1
    · intro hy x hx
      have h1 := hy (cw i x) ((hmem' x).2 hx)
      rw [hform] at h1
      exact (hrange _).1 h1

theorem span_fg_of_denom (a : 𝓞 E) (ha : a ≠ 0) (A : Set E) (hA : ∀ r ∈ A, IsIntegral ℤ ((a : E) * r)) :
    (Submodule.span (𝓞 E) A).FG := by
  have ha' : (a : E) ≠ 0 := by simpa using ha
  have hfg : (Submodule.span (𝓞 E) {(a : E)⁻¹}).FG := ⟨{(a : E)⁻¹}, by simp⟩
  have hN : IsNoetherian (𝓞 E) (Submodule.span (𝓞 E) {(a : E)⁻¹}) := by
    haveI : Module.Finite (𝓞 E) (Submodule.span (𝓞 E) {(a : E)⁻¹}) := Module.Finite.iff_fg.2 hfg
    infer_instance
  refine isNoetherian_submodule.1 hN _ ?_
  rw [Submodule.span_le]
  intro r hr
  rw [SetLike.mem_coe, Submodule.mem_span_singleton]
  obtain ⟨z, hz⟩ : ∃ z : 𝓞 E, (z : E) = (a : E) * r := ⟨⟨_, hA r hr⟩, rfl⟩
  refine ⟨z, ?_⟩
  rw [Algebra.smul_def]
  change (z : E) * (a : E)⁻¹ = r
  rw [hz]
  field_simp

end Gen

section Comparison₂

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts} {Y : DivX D} {cX : ExtraC}

theorem tie_sd {ex : Extra D L hT Gi Gl K Y cX} (t : KerEntTied ex) (u μ i c) : IsSdLat ((t.rd u μ).N i c) := by
  letI := D.host.cmStar
  have h : IsSDLat D.host.E _ (t.seam.lat ((t.rd u μ).N i c)) := t.O_lat u μ i c ▸ ((t.O u μ).lat i c).2
  exact isSdLat_of_transport t.seam.iE (fun x => by rw [t.seam_ok.2 x]; exact (Examples₂.star_eq_conj _ _).symm) _ h

theorem tie_AA_fg {ex : Extra D L hT Gi Gl K Y cX} (t : KerEntTied ex) : t.amb.AA.FG := by
  obtain ⟨b, hb, hfr⟩ := D.host.AA0.isFractional
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha : (RingOfIntegers.mapRingEquiv t.seam.iE).symm b ≠ 0 := by simpa using hb0
  refine span_fg_of_denom _ ha _ ?_
  rintro r ⟨c, hc, s, hs, rfl⟩
  obtain ⟨w, hw⟩ := hfr s hs
  have hw' : (w : D.host.E) = (b : D.host.E) * s := by
    rw [← Algebra.smul_def]; exact hw
  rw [coe_iO_symm, ← map_mul]
  have hcI : IsIntegral ℤ ((((c : 𝓞 D.host.K) : D.host.K) : D.host.E)) :=
    (NumberField.RingOfIntegers.isIntegral_coe c).map ((IntermediateField.val D.host.K).restrictScalars ℤ)
  have e : (b : D.host.E) * ((((c : 𝓞 D.host.K) : D.host.K) : D.host.E) * s) = (((c : 𝓞 D.host.K) : D.host.K) : D.host.E) * w := by
    rw [hw']; ring
  rw [e]
  exact (hcI.mul (NumberField.RingOfIntegers.isIntegral_coe w)).map (t.seam.iE.symm : D.host.E →+* t.X.E).toIntAlgHom

end Comparison₂

end GlobalTheory.TieLat

theorem GlobalTheory.TieLat.tie_AA_fg_and_sd : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), t.amb.AA.FG ∧ ∀ u μ i c, IsSdLat ((t.rd u μ).N i c) :=
  fun _ _ _ _ _ _ _ _ _ t => ⟨GlobalTheory.TieLat.tie_AA_fg t, fun u μ i c => GlobalTheory.TieLat.tie_sd t u μ i c⟩
