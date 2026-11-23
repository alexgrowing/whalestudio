import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.CovCmp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularLocalStatementStatement
open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.Toroidal
open GlobalTheory.VertCmp GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.CovCmp
open scoped Classical

namespace UpperTheory.SpecialPointValuations

private theorem unitAt_fnMap {X Z : Scheme.{0}} [IsIntegral X] [IsIntegral Z] (g : Z ⟶ X)
    (hη : g (genericPoint Z) ⤳ genericPoint X) {z : Z} {t : X.functionField} (h : UnitAt (g z) t) :
    UnitAt z (SmallSec.fnMap g hη t) := by
  obtain ⟨U, hx, s, rfl⟩ := h.regAt.exists_fnOf
  have hy : z ∈ g ⁻¹ᵁ U := hx
  rw [SmallSec.fnMap_fnOf g hη _ (gen_mem hy), unitAt_fnOf_iff hy, ← Scheme.preimage_basicOpen]
  exact (unitAt_fnOf_iff hx _ s).1 h

private theorem unitAt_pow {X : Scheme.{0}} [IsIntegral X] {x : X} {f : X.functionField} (h : UnitAt x f) (m : ℕ) :
    UnitAt x (f ^ m) :=
  have ⟨a, ha, e⟩ := h; ⟨a ^ m, ha.pow m, by rw [map_pow, e]⟩

private theorem unitAt_div {X : Scheme.{0}} [IsIntegral X] {L : LB X} {s : L.ι → X.functionFieldˣ} (hs : IsRatSec L s)
    {x : X} {i j : L.ι} (hi : x ∈ L.U i) (hj : x ∈ L.U j) : UnitAt x ((s i : X.functionField) / s j) := by
  have hx : x ∈ L.U i ⊓ L.U j := ⟨hi, hj⟩
  rw [hs i j (gen_mem hx), mul_div_cancel_right₀ _ (s j).ne_zero]
  exact unitAt_fnOf hx _ _

private theorem valAt_inv {K : Type} [Field K] {Z : Scheme.{0}} [IsIntegral Z] {y : Sp K ⟶ Z} {f : Z.functionField}
    (h : UnitAt (below y) f) : valAt y f⁻¹ = (valAt y f)⁻¹ := by
  simpa using (Base.valAt_zpow y h).2 (-1)

private theorem exists_unit_open {X : Scheme.{0}} [IsIntegral X] (f : X.functionFieldˣ) :
    ∃ U : X.Opens, genericPoint X ∈ U ∧ ∀ y ∈ U, UnitAt y (f : X.functionField) := by
  have h : UnitAt (genericPoint X) (f : X.functionField) := GlobalTheory.Cartier.unitAt_genericPoint f.ne_zero
  exact h.exists_nhds

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

private theorem exists_special (V : Mean4O.Cover Y) (x : V.X) :
    ∃ (x₀ : V.X) (v : HeightOneSpectrum (𝓞 F)), x ⤳ x₀ ∧ (V.p x₀).asIdeal = v.asIdeal := by
  have : IsProper V.p := by
    obtain ⟨n, c, hc, h⟩ := V.ar.isProjOver
    have := isProper_str (𝓞 F) n
    rw [← h]
    infer_instance
  have hc : IsClosed (V.p '' closure {x}) := V.p.isClosedMap _ isClosed_closure
  have h₁ : V.p x ∈ V.p '' closure {x} := ⟨x, subset_closure rfl, rfl⟩
  obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal _ (V.p x).isPrime.ne_top
  have hsp : V.p x ⤳ (⟨𝔪, h𝔪.isPrime⟩ : PrimeSpectrum (𝓞 F)) :=
    (PrimeSpectrum.le_iff_specializes _ _).1 hle
  obtain ⟨x₀, h, e⟩ := hsp.mem_closed hc h₁
  refine ⟨x₀, ⟨𝔪, h𝔪.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField h𝔪 (RingOfIntegers.not_isField F)⟩,
    specializes_iff_mem_closure.2 h, ?_⟩
  rw [e]

private theorem exists_over (V : Mean4O.Cover Y) (W : Y.X.Opens) (hW : genericPoint Y.X ∈ W) :
    ∃ t : V.X.Opens, genericPoint V.X ∈ t ∧ ∀ w : V.G, V.j w ∈ t → V.π w ∈ W := by
  have hj : IsPreimmersion V.j :=
    MorphismProperty.of_isPullback V.pb.flip (IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 F)) (S := F))
  obtain ⟨t, ht, htW⟩ := V.j.isEmbedding.isInducing.isOpen_iff.1 (V.π ⁻¹ᵁ W).isOpen
  obtain ⟨w, hw⟩ := V.π.surjective (genericPoint Y.X)
  have hwt : V.j w ∈ t := by
    have : w ∈ (V.π ⁻¹ᵁ W : Set V.G) := by
      change V.π w ∈ W
      rw [hw]; exact hW
    rw [← htW] at this
    exact this
  refine ⟨⟨t, ht⟩, ((genericPoint_spec V.X).mem_open_set_iff ht).2 ⟨_, trivial, hwt⟩, fun w hw => ?_⟩
  have : w ∈ (V.π ⁻¹ᵁ W : Set V.G) := by
    rw [← htW]; exact hw
  exact this

private theorem read_up {V V₁ : Mean4O.Cover Y} {π₁ : V.X ⟶ V₁.X} (hl : Lies V V₁ π₁)
    (h₁ : π₁ (genericPoint V.X) ⤳ genericPoint V₁.X) {L : LB V₁.X} {s : L.ι → V₁.X.functionFieldˣ}
    {v : HeightOneSpectrum (𝓞 F)} {l : TrueGeo.Ext v → AlgPt Y → ℝ} (h : CRead V₁ v L s l) (i : L.ι) :
    ∃ t : V.X.Opens, genericPoint V.X ∈ t ∧
      ∀ (e : TrueGeo.Ext v) (y : AlgPt Y) (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X),
        z ≫ V.π = y.1 → spMap e.O.subtype ≫ yt = z ≫ V.j → ⊤ ≤ yt ⁻¹ᵁ (π₁ ⁻¹ᵁ L.U i) → below (z ≫ V.j) ∈ t →
        UnitAt (below (z ≫ V.j)) (SmallSec.fnMap π₁ h₁ (s i : V₁.X.functionField)) ∧
        Real.log (e.w (TrueGeo.valAt (z ≫ V.j) (SmallSec.fnMap π₁ h₁ (s i : V₁.X.functionField)))) = l e y := by
  obtain ⟨g, hg₁, hg₂⟩ := hl
  obtain ⟨-, W, hW, hR⟩ := h
  obtain ⟨t, ht, htW⟩ := exists_over V W hW
  obtain ⟨U, hU, hUu⟩ := exists_unit_open (s i)
  refine ⟨t ⊓ π₁ ⁻¹ᵁ U, ⟨ht, h₁.mem_open U.isOpen hU⟩, fun e y z yt hz hyt hV hb => ?_⟩
  have hj : (z ≫ g) ≫ V₁.j = (z ≫ V.j) ≫ π₁ := by rw [Category.assoc, hg₁, Category.assoc]
  have hu : UnitAt (below ((z ≫ V.j) ≫ π₁)) (s i : V₁.X.functionField) := hUu _ hb.2
  have hy : below y.1 ∈ W := by
    rw [← hz]
    exact htW (below z) hb.1
  have a := hR e y (z ≫ g) (yt ≫ π₁) i hy (by rw [Category.assoc, hg₂, hz])
    (by rw [hj, ← Category.assoc, hyt]) (fun q hq => hV hq) (by rw [hj]; exact hu)
  rw [hj] at a
  refine ⟨unitAt_fnMap π₁ h₁ (z := below (z ≫ V.j)) hu, ?_⟩
  rw [SmallSec.valAt_fnMap π₁ h₁ _ hu.regAt]
  exact a

end UpperTheory.SpecialPointValuations

open UpperTheory.SpecialPointValuations in
theorem UpperTheory.comparison_of_line_bundle_sections :
    ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V V₁ V₂ : Mean4O.Cover Y) (π₁ : V.X ⟶ V₁.X) (π₂ : V.X ⟶ V₂.X), Lies V V₁ π₁ → Lies V V₂ π₂ → ∀ (h₁ : π₁ (genericPoint V.X) ⤳ genericPoint V₁.X) (h₂ : π₂ (genericPoint V.X) ⤳ genericPoint V₂.X) (L₁ : LB V₁.X), L₁.IsLB → ∀ (s₁ : L₁.ι → V₁.X.functionFieldˣ) (L₂ : LB V₂.X), L₂.IsLB → ∀ (s₂ : L₂.ι → V₂.X.functionFieldˣ) (l : ∀ v : HeightOneSpectrum (𝓞 F), TrueGeo.Ext v → AlgPt Y → ℝ) (m₁ m₂ : ℕ), (∀ v, CRead V₁ v L₁ s₁ fun e y => (m₁ : ℝ) * l v e y) → (∀ v, CRead V₂ v L₂ s₂ fun e y => (m₂ : ℝ) * l v e y) → ∀ (x : V.X) (i₁ : L₁.ι) (i₂ : L₂.ι), π₁ x ∈ L₁.U i₁ → π₂ x ∈ L₂.U i₂ → UnitAt x (SmallSec.fnMap π₁ h₁ (s₁ i₁ : V₁.X.functionField) ^ m₂ / SmallSec.fnMap π₂ h₂ (s₂ i₂ : V₂.X.functionField) ^ m₁) := by
  intro F _ _ Y V V₁ V₂ π₁ π₂ hl₁ hl₂ h₁ h₂ L₁ hL₁ s₁ L₂ hL₂ s₂ l m₁ m₂ hR₁ hR₂
  have key : ∀ (v : HeightOneSpectrum (𝓞 F)) (x : V.X) (i₁ : L₁.ι) (i₂ : L₂.ι), (V.p x).asIdeal = v.asIdeal →
      π₁ x ∈ L₁.U i₁ → π₂ x ∈ L₂.U i₂ →
      UnitAt x (SmallSec.fnMap π₁ h₁ (s₁ i₁ : V₁.X.functionField) ^ m₂ /
        SmallSec.fnMap π₂ h₂ (s₂ i₂ : V₂.X.functionField) ^ m₁) := by
    intro v x i₁ i₂ hx hi₁ hi₂
    set u := SmallSec.fnMap π₁ h₁ (s₁ i₁ : V₁.X.functionField) ^ m₂ /
        SmallSec.fnMap π₂ h₂ (s₂ i₂ : V₂.X.functionField) ^ m₁ with hu
    have hu0 : u ≠ 0 := div_ne_zero (pow_ne_zero _ ((map_ne_zero _).2 (s₁ i₁).ne_zero))
      (pow_ne_zero _ ((map_ne_zero _).2 (s₂ i₂).ne_zero))
    obtain ⟨t₁, ht₁, H₁⟩ := read_up hl₁ h₁ (hR₁ v) i₁
    obtain ⟨t₂, ht₂, H₂⟩ := read_up hl₂ h₂ (hR₂ v) i₂
    have main : ∀ (e : TrueGeo.Ext v) (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X),
        z ≫ V.π ≫ Y.str = spMap (algebraMap F (AlgebraicClosure F)) → spMap e.O.subtype ≫ yt = z ≫ V.j →
        ⊤ ≤ yt ⁻¹ᵁ (π₁ ⁻¹ᵁ L₁.U i₁ ⊓ π₂ ⁻¹ᵁ L₂.U i₂) → below (z ≫ V.j) ∈ t₁ ⊓ t₂ →
        UnitAt (below (z ≫ V.j)) u ∧ e.w (TrueGeo.valAt (z ≫ V.j) u) = 1 := by
      intro e z yt hz hyt hV hb
      let y : AlgPt Y := ⟨z ≫ V.π, by rw [Category.assoc]; exact hz⟩
      obtain ⟨a₁, a₂⟩ := H₁ e y z yt rfl hyt (fun q hq => (hV hq).1) hb.1
      obtain ⟨b₁, b₂⟩ := H₂ e y z yt rfl hyt (fun q hq => (hV hq).2) hb.2
      have c₁ := unitAt_pow a₁ m₂
      have c₂ := unitAt_pow b₁ m₁
      refine ⟨by rw [hu, div_eq_mul_inv]; exact c₁.mul c₂.inv, ?_⟩
      rw [hu, div_eq_mul_inv, SmallSec.valAt_mul c₁.regAt c₂.inv.regAt, valAt_inv c₂, SmallSec.valAt_pow a₁.regAt,
        SmallSec.valAt_pow b₁.regAt, map_mul, map_inv₀, map_pow, map_pow]
      have p₁ := e.w.pos (SmallSec.valAt_ne_zero a₁)
      have p₂ := e.w.pos (SmallSec.valAt_ne_zero b₁)
      rw [mul_inv_eq_one₀ (pow_pos p₂ m₁).ne']
      refine Real.log_injOn_pos (pow_pos p₁ m₂) (pow_pos p₂ m₁) ?_
      rw [Real.log_pow, Real.log_pow, a₂, b₂]
      ring
    have hne : ((t₁ ⊓ t₂ : V.X.Opens) : Set V.X).Nonempty := ⟨genericPoint V.X, ht₁, ht₂⟩
    refine (GlobalTheory.Cartier.unitAt_iff hu0).2 ⟨?_, ?_⟩
    · exact GlobalTheory.T.RegularLocalStatement F Y V (π₁ ⁻¹ᵁ L₁.U i₁ ⊓ π₂ ⁻¹ᵁ L₂.U i₂) (t₁ ⊓ t₂) hne v u
        (fun e z yt a b c d => (main e z yt a b c d).2.le) x ⟨hi₁, hi₂⟩ hx
    · refine GlobalTheory.T.RegularLocalStatement F Y V (π₁ ⁻¹ᵁ L₁.U i₁ ⊓ π₂ ⁻¹ᵁ L₂.U i₂) (t₁ ⊓ t₂) hne v u⁻¹
        (fun e z yt a b c d => ?_) x ⟨hi₁, hi₂⟩ hx
      obtain ⟨k₁, k₂⟩ := main e z yt a b c d
      rw [valAt_inv k₁, map_inv₀, k₂, inv_one]
  intro x i₁ i₂ hi₁ hi₂
  obtain ⟨x₀, v, hx, hx₀⟩ := exists_special V x
  obtain ⟨j₁, hj₁⟩ := exists_chart hL₁ (π₁ x₀)
  obtain ⟨j₂, hj₂⟩ := exists_chart hL₂ (π₂ x₀)
  obtain ⟨U, hU, hUu⟩ := (key v x₀ j₁ j₂ hx₀ hj₁ hj₂).exists_nhds
  have k₁ := hUu x (hx.mem_open U.isOpen hU)
  have k₂ := unitAt_pow (unitAt_fnMap π₁ h₁
    (unitAt_div (hR₁ v).1 hi₁ ((hx.map π₁.continuous).mem_open (L₁.U j₁).isOpen hj₁))) m₂
  have k₃ := unitAt_pow (unitAt_fnMap π₂ h₂
    (unitAt_div (hR₂ v).1 ((hx.map π₂.continuous).mem_open (L₂.U j₂).isOpen hj₂) hi₂)) m₁
  have k₄ := (k₁.mul k₂).mul k₃
  have n₁ : SmallSec.fnMap π₁ h₁ (s₁ j₁ : V₁.X.functionField) ≠ 0 := (map_ne_zero _).2 (s₁ j₁).ne_zero
  have n₂ : SmallSec.fnMap π₂ h₂ (s₂ j₂ : V₂.X.functionField) ≠ 0 := (map_ne_zero _).2 (s₂ j₂).ne_zero
  have n₃ : SmallSec.fnMap π₂ h₂ (s₂ i₂ : V₂.X.functionField) ≠ 0 := (map_ne_zero _).2 (s₂ i₂).ne_zero
  convert k₄ using 1
  rw [map_div₀, map_div₀, div_pow, div_pow]
  field_simp
