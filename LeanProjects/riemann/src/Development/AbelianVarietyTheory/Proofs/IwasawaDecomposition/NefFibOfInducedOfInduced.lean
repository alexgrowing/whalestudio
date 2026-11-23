import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingKrullDimLeOfIsAlgebraic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RatIsom
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalIsometryIsometric
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InducedMetricPullback
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InducedMetricPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InducedMetricShiftElement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InducedMetricDifferenceLog
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LogAbsoluteValueRational
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsElementHeightDifference
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RatIsomOfInducedHermitianBundles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibPowIffStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibPullbackStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfSurjectivePullbackStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.HermIsom Formalism.BasicNotions

namespace GlobalTheory.TrueGeo.NefFibUniq

theorem nefFib_shift {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} (L : HermLB p) (t : (k →+* ℂ) → ℝ)
    (ht : ∀ σ, t ((starRingEnd ℂ).comp σ) = t σ) : ArInt.NefFib (L.shift t ht) ↔ ArInt.NefFib L := Iff.rfl

theorem nefFib_iff_of_isometric {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {L L' : HermLB p}
    (h : L.Isometric L') : ArInt.NefFib L ↔ ArInt.NefFib L' := by
  obtain ⟨w, hw, -⟩ := h
  have e : cls L.B L.isLB = cls L'.B L'.isLB := (cls_eq_iff _ _).2 ⟨w, hw⟩
  have key : ∀ (Z : Scheme.{0}) (i : Z ⟶ X) (κ : Type) [Field κ] [Algebra κ Γ(Z, ⊤)],
      topSelfIntersection κ (L.B.pull i) 1 = topSelfIntersection κ (L'.B.pull i) 1 := fun Z i κ _ _ =>
    interNum_congr_cls κ _ (fun _ => LB.isLB_pull L.isLB i) (fun _ => LB.isLB_pull L'.isLB i) fun _ => by
      rw [cls_pull L.isLB, cls_pull L'.isLB, e]
  constructor <;> intro H Z i _ _ κ _ _ _ hd
  · rw [← key]; exact H Z i κ hd
  · rw [key]; exact H Z i κ hd

variable {F : Type} [Field F] [NumberField F] {C : CxSt F} {Y : Var F} {A : Adl C Y}

theorem surjective_of_models (M N : TrueGeo.Model Y) (π : N.X ⟶ M.X) (hπ : π ≫ M.p = N.p)
    (hU : ∃ U : M.X.Opens, (U : Set M.X).Nonempty ∧ IsIso (π ∣_ U)) : Function.Surjective π := by
  obtain ⟨U, hne, hi⟩ := hU
  have := M.ar.isIntegral
  have := N.ar.isIntegral
  have : IsProper M.p := CommonModel.isProper_of_isProjOver M.ar.isProjOver
  have : IsProper N.p := CommonModel.isProper_of_isProjOver N.ar.isProjOver
  have : IsProper (π ≫ M.p) := by rw [hπ]; infer_instance
  have : IsProper π := IsProper.of_comp π M.p
  obtain ⟨_, _⟩ := birational_of_isIso_morphismRestrict π U hne.to_subtype
  exact (surjective_of_isDominant_of_isClosed_range π π.isClosedMap.isClosed_range).surj

theorem nefFib_of_induced_of_induced (N : TrueGeo.Model Y) (hN : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme N.X)
    {L L' : HermLB N.p} {k : ℕ+} {cf cf' : HeightOneSpectrum (𝓞 F) → ℝ}
    (h : A.Induced N L k cf) (h' : A.Induced N L' k cf') (hL' : ArInt.NefFib L') : ArInt.NefFib L := by
  have hint := N.ar.isIntegral
  have hproj := N.ar.isProjOver
  obtain ⟨m, b, b', hb, hb', e⟩ := GlobalTheory.exists_mul_eq_log_adicAbv_sub F (fun v => ((k : ℕ) : ℝ) * (A.n : ℕ) * (cf' v - cf v))
    ((h.1.union h'.1).subset fun v hv => by
      by_contra h0
      simp only [Set.mem_union, Function.mem_support, not_or, not_not] at h0
      simp [h0.1, h0.2] at hv) fun v => by
    obtain ⟨e, α, hα, h₁⟩ := GlobalTheory.TrueGeo.ValGroup.main F C Y A N L L' k cf cf' h h' v
    rw [h₁]
    exact GlobalTheory.ExtValueGroup.log_w_rat F v e α hα
  have hc : ∀ σ : 𝓞 F →+* ℂ, Real.log ‖((starRingEnd ℂ).comp σ) b‖ = Real.log ‖σ b‖ := fun σ => by simp
  have hc' : ∀ σ : 𝓞 F →+* ℂ, Real.log ‖((starRingEnd ℂ).comp σ) b'‖ = Real.log ‖σ b'‖ := fun σ => by simp
  have h₁ := GlobalTheory.TrueGeo.IndScale.induced_shift F C Y A N (L.pow m) (k * m) cf b hb hc (GlobalTheory.TrueGeo.InducedPow.induced_pow F C Y A N L k m cf h)
  have h₂ := GlobalTheory.TrueGeo.IndScale.induced_shift F C Y A N (L'.pow m) (k * m) cf' b' hb' hc' (GlobalTheory.TrueGeo.InducedPow.induced_pow F C Y A N L' k m cf' h')
  have hm : ((m : ℕ) : ℝ) ≠ 0 := by exact_mod_cast m.ne_zero
  have hk : ((k : ℕ) : ℝ) ≠ 0 := by exact_mod_cast k.ne_zero
  have hn : ((A.n : ℕ) : ℝ) ≠ 0 := by exact_mod_cast A.n.ne_zero
  have h₂' : A.Induced N ((L'.pow m).shift (fun σ => Real.log ‖σ b'‖) hc') (k * m) fun v => cf v +
      Real.log (NumberField.HeightOneSpectrum.adicAbv F v (algebraMap (𝓞 F) F b)) / ((((k * m : ℕ+) : ℕ) : ℝ) * (A.n : ℕ)) := by
    convert h₂ using 2 with v
    rw [sub_eq_iff_eq_add.1 (e v).symm, PNat.mul_coe, Nat.cast_mul]
    field_simp
    ring
  have hR := GlobalTheory.TrueGeo.InducedIsom.ratIsom_of_induced F C Y A N hN _ _ (k * m) _ h₁ h₂'
  have hIso := GlobalTheory.HermIsom.isometric_of_ratIsom _ N.X N.p _ _ hR
  have hL'm : ArInt.NefFib ((L'.pow m).shift (fun σ => Real.log ‖σ b'‖) hc') :=
    (nefFib_shift _ _ _).2 ((GlobalTheory.T.nefFib_pow_iff' _ N.X N.p hproj L' m m.pos).2 hL')
  exact (GlobalTheory.T.nefFib_pow_iff' _ N.X N.p hproj L m m.pos).1 ((nefFib_shift _ _ _).1 ((nefFib_iff_of_isometric hIso).2 hL'm))

theorem nefFib_of_induced : ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (A : Adl C Y)
    (M : TrueGeo.Model Y) (L : HermLB M.p) (k : ℕ+) (cf : HeightOneSpectrum (𝓞 F) → ℝ),
    A.Induced M L k cf → A.NefFib → ArInt.NefFib L := by
  rintro F _ _ C Y A M L k cf hI ⟨M', L', k', cf', hI', hN'⟩
  obtain ⟨N, π, π', hN, hπ, hπ', hj, hj', hU, hU'⟩ := GlobalTheory.ModelDom.exists_normal_dominating F Y M M'
  have := M.ar.isIntegral
  have := M'.ar.isIntegral
  have := N.ar.isIntegral
  have h₁ := GlobalTheory.TrueGeo.InducedPow.induced_pow F C Y A N _ k k' cf (GlobalTheory.TrueGeo.InducedPull.induced_pull F C Y A M N π hπ hj L k cf hI)
  have h₂ := GlobalTheory.TrueGeo.InducedPow.induced_pow F C Y A N _ k' k cf' (GlobalTheory.TrueGeo.InducedPull.induced_pull F C Y A M' N π' hπ' hj' L' k' cf' hI')
  rw [mul_comm k' k] at h₂
  have hN₂ : ArInt.NefFib ((L'.pull π' hπ').pow k) :=
    (GlobalTheory.T.nefFib_pow_iff' _ N.X N.p N.ar.isProjOver _ k k.pos).2 (GlobalTheory.T.nefFib_pullback _ M'.X N.X M'.p N.p M'.ar.isProjOver N.ar.isProjOver π' hπ' L' hN')
  have hN₁ := nefFib_of_induced_of_induced N hN h₁ h₂ hN₂
  exact GlobalTheory.T.nefFib_of_surjective_pullback _ M.X N.X M.p N.p M.ar.isProjOver N.ar.isProjOver π hπ (surjective_of_models M N π hπ hU) L
    ((GlobalTheory.T.nefFib_pow_iff' _ N.X N.p N.ar.isProjOver _ k' k'.pos).1 hN₁)

end GlobalTheory.TrueGeo.NefFibUniq
