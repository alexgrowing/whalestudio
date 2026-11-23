import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfCurveDegreesNonneg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfSurjectivePullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducedModelDominantCurveRestriction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleSectionsAvoidClosedPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsPullbackAlongCover

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.TrueGeo
open scoped ENNReal Classical
open Limits
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.NefHodgeTateAt

namespace GlobalTheory.NefDeRhamCover

section Curves

variable {k : Type} [CommRing k] [Module.Finite ℤ k] {X : Scheme.{0}} {p : X ⟶ Sp k}

theorem topSelf_triv (hp : IsProjOver p) (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] (κ : Type) [Field κ]
    [Finite κ] [Algebra κ Γ(Z, ⊤)] (hd : topologicalKrullDim Z = 1) :
    topSelfIntersection κ ((HermLB.triv p).B.pull i) 1 = 0 := by
  have h0 : cls _ (HermLB.triv p).isLB = 0 :=
    (cls_eq_zero_iff (LB.isLB_triv X)).2 ⟨⟨fun _ => 1⟩, fun _ _ => by simp only [map_one, mul_one]⟩
  have h := topSelf_of_cls_eq_add hp (HermLB.triv p).isLB (HermLB.triv p).isLB (HermLB.triv p).isLB
    (by rw [h0, add_zero]) Z i κ hd
  linarith

theorem topSelf_dual (hp : IsProjOver p) (L : HermLB p) (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] (κ : Type)
    [Field κ] [Finite κ] [Algebra κ Γ(Z, ⊤)] (hd : topologicalKrullDim Z = 1) :
    topSelfIntersection κ (L.dual.B.pull i) 1 = -topSelfIntersection κ (L.B.pull i) 1 := by
  have e1 : cls (L.pow 0).B (L.pow 0).isLB = (0 : ℕ) • cls L.B L.isLB := cls_lbPow L.isLB 0 _
  have e2 : cls L.dual.B L.dual.isLB = -cls L.B L.isLB := cls_dual L.isLB _
  have h := topSelf_of_cls_eq_add hp (L.pow 0).isLB L.isLB L.dual.isLB
    (by rw [e1, e2, zero_smul, add_neg_cancel]) Z i κ hd
  rw [topSelf_pow hp L 0 Z i κ hd] at h
  push_cast at h
  linarith

theorem topSelf_zp (hp : IsProjOver p) (L : HermLB p) (n : ℤ) (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i]
    (κ : Type) [Field κ] [Finite κ] [Algebra κ Γ(Z, ⊤)] (hd : topologicalKrullDim Z = 1) :
    topSelfIntersection κ ((ArInt.zp L n).B.pull i) 1 = n * topSelfIntersection κ (L.B.pull i) 1 := by
  rw [show ArInt.zp L n = (L.pow n.toNat).tens (L.pow (-n).toNat).dual from rfl,
    topSelf_of_cls_eq_add hp ((L.pow n.toNat).tens (L.pow (-n).toNat).dual).isLB (L.pow n.toNat).isLB
      (L.pow (-n).toNat).dual.isLB (cls_tens _ _ _) Z i κ hd,
    topSelf_dual hp _ Z i κ hd, topSelf_pow hp L _ Z i κ hd, topSelf_pow hp L _ Z i κ hd]
  have e : ((n.toNat : ℕ) : ℤ) - ((-n).toNat : ℕ) = n := Int.toNat_sub_toNat_neg n
  linear_combination (topSelfIntersection κ (L.B.pull i) 1) * e

theorem topSelf_comb (hp : IsProjOver p) {ι : Type} [Fintype ι] (R : ι → HermLB p) (n : ι → ℤ) (Z : Scheme.{0})
    (i : Z ⟶ X) [IsClosedImmersion i] (κ : Type) [Field κ] [Finite κ] [Algebra κ Γ(Z, ⊤)]
    (hd : topologicalKrullDim Z = 1) :
    topSelfIntersection κ ((ArInt.comb R n).B.pull i) 1 = ∑ j, n j * topSelfIntersection κ ((R j).B.pull i) 1 := by
  rw [← Finset.sum_map_toList, ArInt.comb]
  induction (Finset.univ : Finset ι).toList with
  | nil => simpa using topSelf_triv hp Z i κ hd
  | cons j l ih =>
    rw [List.foldr_cons, List.map_cons, List.sum_cons, ← ih, ← topSelf_zp hp (R j) (n j) Z i κ hd]
    exact topSelf_of_cls_eq_add hp ((ArInt.zp (R j) (n j)).tens
      (List.foldr (fun i M => (ArInt.zp (R i) (n i)).tens M) (HermLB.triv p) l)).isLB (ArInt.zp (R j) (n j)).isLB
      (List.foldr (fun i M => (ArInt.zp (R i) (n i)).tens M) (HermLB.triv p) l).isLB (cls_tens _ _ _) Z i κ hd

omit [Module.Finite ℤ k] in

theorem topSelf_of_cls_eq {L M : HermLB p} (h : cls L.B L.isLB = cls M.B M.isLB) (Z : Scheme.{0}) (i : Z ⟶ X)
    (κ : Type) [Field κ] [Algebra κ Γ(Z, ⊤)] : topSelfIntersection κ (L.B.pull i) 1 = topSelfIntersection κ (M.B.pull i) 1 :=
  interNum_congr_cls κ _ (fun _ => LB.isLB_pull L.isLB i) (fun _ => LB.isLB_pull M.isLB i) fun _ => by
    rw [cls_pull L.isLB, cls_pull M.isLB, h]

end Curves

section Covers

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

theorem cls_pow_eq_of_norms {V : Cover Y} {L L' : HermLB V.p} {f : Y.X → Y.Fn} {a a' : ∀ σ : F →+* ℂ, Pts Y σ → ℝ}
    {l : ∀ v : HeightOneSpectrum (𝓞 F), Ext v → AlgPt Y → ℝ} {c : HeightOneSpectrum (𝓞 F) → ℝ}
    (hc : (Function.support c).Finite) (h : Norms V L f a fun v e y => l v e y + c v) (h' : Norms V L' f a' l) :
    ∃ m : ℕ, 0 < m ∧ cls (L.pow m).B (L.pow m).isLB = cls (L'.pow m).B (L'.pow m).isLB := by
  obtain ⟨m, b, b', hb, hb', E⟩ := GlobalTheory.exists_mul_eq_log_adicAbv_sub F c hc fun v => by
    obtain ⟨e⟩ : Nonempty (Ext v) := inferInstance
    obtain ⟨y, z, yt, e₁, e₂⟩ := exists_integral_point V v e
    obtain ⟨r, -, -, -, hf⟩ := h
    obtain ⟨r', -, -, -, hf'⟩ := h'
    have chart (B : HermLB V.p) : ∃ i, ⊤ ≤ yt ⁻¹ᵁ B.B.U i := by
      obtain ⟨i, hi⟩ := exists_chart B.isLB (yt (IsLocalRing.closedPoint e.O))
      exact ⟨i, ((IsLocalRing.closedPoint_mem_iff (R := e.O) (yt ⁻¹ᵁ B.B.U i)).1 hi).ge⟩
    obtain ⟨i, hi⟩ := chart L
    obtain ⟨i', hi'⟩ := chart L'
    have h₁ := hf v e y z yt (fun _ => i) e₁ e₂ hi
    have h₂ := hf' v e y z yt (fun _ => i') e₁ e₂ hi'
    obtain ⟨α, hα, h₃⟩ := ValGroup.exists_log_sub e.w
      (valAt z (V.φ (f (below y.1)) * (r' fun _ => i' : V.G.functionFieldˣ)))
      (valAt z (V.φ (f (below y.1)) * (r fun _ => i : V.G.functionFieldˣ)))
    have : c v = Real.log (e.w α) := by
      rw [← h₃, ← h₁, ← h₂]
      ring
    rw [this]
    exact GlobalTheory.ExtValueGroup.log_w_rat F v e α hα
  have ne {x : 𝓞 F} (hx : x ≠ 0) : algebraMap (𝓞 F) F x ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).2 hx
  obtain ⟨a₁, h₁⟩ := norms_scale (norms_pow F Y V L _ _ _ m h) (ne hb')
  obtain ⟨a₂, h₂⟩ := norms_scale (norms_pow F Y V L' _ _ _ m h') (ne hb)
  exact ⟨m, m.pos, cls_eq_of_norms h₁ (h₂.congr (fun _ => rfl) (fun _ _ => rfl) fun v e y => by
    linear_combination -E v)⟩

end Covers

theorem exists_cover_degree_eq : Hypotheses2 → HypothesesH → ∀ (D : D7) (O : Setup D), O.Core → ∀ (A : SlopeTestRemainingChoices O.Y) (T : Real0 O.Y) (H : Ht O.Y) (h : O.Reads A T H),
  ∀ (B : ℝ), 2 ≤ B → ∀ (u : Wt O.Y) (s : ℚ), IsRat O.Y u → 0 < s → WeightThresholdDefs.Dominant O.Y (A.sh u s) →
  ∀ (c : O.s.Comp) (M : TrueGeo.Model (O.var c)) (L : HermLB M.p) (k : ℕ+) (cf : HeightOneSpectrum (𝓞 D.what₂.LL) → ℝ),
  (O.Mb B u s c).Induced M L k cf → ∀ (q : ℕ) [Fact q.Prime],
  ∃ (X' : Scheme.{0}) (p' : X' ⟶ Sp (𝓞 D.what₂.LL)) (π : X' ⟶ M.X) (hπ : π ≫ M.p = p')
    (ρ : X' ⟶ (h.mdl (FlagAr.setB O.Y B) c).V.X) (hρ : ρ ≫ (h.mdl (FlagAr.setB O.Y B) c).V.p = p'),
    IsProjOver p' ∧ Function.Surjective π ∧ ∃ (κ a : ℝ), 0 < κ ∧ 0 ≤ a ∧
    ∀ (Z : Scheme.{0}) (i : Z ⟶ X') [IsClosedImmersion i] [IsIntegral Z] [Algebra (ZMod q) Γ(Z, ⊤)],
      topologicalKrullDim Z = 1 →
      κ * (topSelfIntersection (ZMod q) ((L.pull π hπ).B.pull i) 1 : ℝ) =
        a * (topSelfIntersection (ZMod q) (((h.mdl (FlagAr.setB O.Y B) c).amp.pull ρ hρ).B.pull i) 1 : ℝ) +
        ∑ x, -(A.sh u s x.1 x.2) *
          (topSelfIntersection (ZMod q) ((((h.mdl (FlagAr.setB O.Y B) c).root (FlagAr.setB O.Y B) x).pull ρ hρ).B.pull i) 1 : ℝ) := by
  intro hP hH D O hO A T H h B hB u s hu hs hdom c M L k cf hI q _
  obtain ⟨m, b, hm, hb, hD, -, hfin⟩ := hO.mbIs B hB u s hu hs (A.sh u s)
    (by rw [← h.aux.dir]; rfl) hdom c
  set W := h.mdl (FlagAr.setB O.Y B) c with hW
  obtain ⟨P, π₀, -, hPn, hπ₀, -, hj, -, hU, -⟩ := GlobalTheory.ModelDom.exists_normal_dominating _ _ M M
  have h₁ := InducedPull.induced_pull _ _ _ _ M P π₀ hπ₀ hj L k cf hI
  have h₂ := h₁.twist_fin (c := -cf) (by rw [Function.support_neg]; exact hI.1)
  rw [add_neg_cancel] at h₂
  have h₃ := norms_of_induces (Cover.induces_ofModel hPn h₂)
  obtain ⟨V', a, g, b', ha, hb', e₁, e₂, e₃, e₄⟩ := CoverDom.exists_cover_dominating _ _ W.V P
  have hη : V'.π (genericPoint V'.G) = genericPoint (O.var c).X := by
    have := (genericPoint_spec V'.G).image V'.π.continuous
    rw [Set.image_univ, V'.π.surjective.range_eq, closure_univ] at this
    exact this.eq (genericPoint_spec _)
  have h₄ := norms_pull _ _ (Cover.ofModel P hPn) V' b' hb' V'.π e₄ (Category.comp_id _) hη _ _ _ _ h₃
  have hbη := (CoverDeg.map_genericPoint_and_deg _ _ (Cover.ofModel P hPn) V' b' hb' V'.π e₄
    (Category.comp_id _) hη).1
  have hamp := norms_pull _ _ W.V V' a ha g e₁ e₂ e₃ _ _ _ _ (norms_of_induces W.amp_spec)
  have hR : ∀ x, Norms V' ((W.root (FlagAr.setB O.Y B) x).pull a ha)
      (fun z => genAt (O.root0 c (FlagAr.setB O.Y B) x).D z)
      (fun σ y => lnAdl (O.root0 c (FlagAr.setB O.Y B) x) σ y)
      (fun v e y => (O.root0 c (FlagAr.setB O.Y B) x).lg v e y) := fun x =>
    (norms_pull _ _ W.V V' a ha g e₁ e₂ e₃ _ _ _ _
      (norms_of_induces (Setup.induces_root0 D O hO.dualRef _ c W _ subset_rfl x))).congr
      (fun _ => pow_one _) (fun _ _ => by simp) fun _ _ _ => by simp
  have hmn : (0 : ℝ) < (m : ℝ) * ((O.Mb B u s c).n : ℕ) :=
    mul_pos (Nat.cast_pos.2 hm) (Nat.cast_pos.2 (O.Mb B u s c).n.2)
  have hb0 : 0 ≤ b none := by
    have h₁ : (m : ℝ) * ((O.Mb B u s c).n : ℕ) * (s : ℝ) = b none * ((O.met.ab c).n : ℕ) := hb none
    have h₂ : (0 : ℝ) < b none * ((O.met.ab c).n : ℕ) := h₁ ▸ mul_pos hmn (by exact_mod_cast hs)
    have h₃ : (0 : ℝ) < b none := by
      by_contra hh
      push Not at hh
      nlinarith [(Nat.cast_nonneg ((O.met.ab c).n : ℕ) : (0 : ℝ) ≤ _)]
    exact_mod_cast h₃.le
  have hbx (x : DV.Rt D.what₂.Tau O.N) : (m : ℝ) * ((O.Mb B u s c).n : ℕ) * -A.sh u s x.1 x.2 = b (some x) :=
    (hb (some x)).trans (by
      change _ * (((1 : ℕ+) : ℕ) : ℝ) = _
      simp)
  have hN := norms_tens _ _ V' _ _ _ _ _ _ _ _ (norms_pow _ _ V' _ _ _ _ (b none).toNat hamp)
    (norms_pow _ _ V' _ _ _ _ W.k (norms_comb hR fun x => b (some x)))
  have hc : (((b none).toNat : ℕ) : ℝ) = b none := by exact_mod_cast Int.toNat_of_nonneg hb0
  obtain ⟨a', ha'⟩ := norms_of_comb (K := W.k) hD hfin (hN.congr (fun x => by
    rw [Fintype.prod_option, mul_pow, ← pow_mul, mul_comm W.k, pow_mul]
    refine congrArg₂ (· * ·) (congrArg (· ^ W.k) ?_) rfl
    rw [← zpow_natCast, Int.toNat_of_nonneg hb0]
    rfl) (fun _ _ => rfl) fun v e y => by
    rw [Fintype.sum_option, hc]
    simp only [Option.elim]
    ring)
  have h₅ := norms_pow _ _ V' _ _ _ _ (W.k * m) h₄
  have h₆ := norms_pow _ _ V' _ _ _ _ (k : ℕ) ha'
  obtain ⟨m', hm', hcl⟩ := cls_pow_eq_of_norms (c := fun v => ((W.k * m : ℕ) : ℝ) * (k : ℕ) * ((O.Mb B u s c).n : ℕ) * cf v)
    (hI.1.subset fun v hv h0 => hv (by simp [h0]))
    (h₅.congr (fun x => by rw [← pow_mul, ← pow_mul, mul_comm]; rfl) (fun _ _ => rfl) fun v e y => by
      simp only [Adl.twist, Pi.neg_apply]
      push_cast
      ring) h₆

  have := P.ar.isIntegral
  have : IsProper P.p := (isProper_and_exists_isAmpleLB_of_isProjOver P.ar.isProjOver).1
  have : IsProper (b' ≫ P.p) := by
    rw [hb']
    exact (isProper_and_exists_isAmpleLB_of_isProjOver V'.ar.isProjOver).1
  have : IsProper b' := IsProper.of_comp b' P.p
  have hbs : Function.Surjective b' := fun x =>
    (genericPoint_specializes x).mem_closed b'.isClosedMap.isClosed_range ⟨_, hbη⟩
  have hs₀ := NefFibUniq.surjective_of_models M P π₀ hπ₀ hU
  have hsurj : Function.Surjective (b' ≫ π₀) := fun x => by
    obtain ⟨y, rfl⟩ := hs₀ x
    obtain ⟨z, rfl⟩ := hbs y
    exact ⟨z, by rw [Scheme.Hom.comp_apply]⟩
  have hn0 : (0 : ℝ) < ((O.Mb B u s c).n : ℕ) := Nat.cast_pos.2 (O.Mb B u s c).n.2
  have hk0 : (0 : ℝ) < (k : ℕ) := Nat.cast_pos.2 k.2
  have hW0 : (0 : ℝ) < W.k := Nat.cast_pos.2 W.k_pos
  have hm0 : (0 : ℝ) < m := Nat.cast_pos.2 hm
  refine ⟨V'.X, V'.p, b' ≫ π₀, by rw [Category.assoc, hπ₀, hb'], a, ha, V'.ar.isProjOver, hsurj,
    1 / ((k : ℕ) * ((O.Mb B u s c).n : ℕ)), (b none : ℝ) / (W.k * m * ((O.Mb B u s c).n : ℕ)),
    by positivity, div_nonneg (by exact_mod_cast hb0) (by positivity), ?_⟩
  intro Z i _ _ _ hd
  have hp := V'.ar.isProjOver
  have e0 : topSelfIntersection (ZMod q) ((L.pull (b' ≫ π₀) (by rw [Category.assoc, hπ₀, hb'])).B.pull i) 1 =
      topSelfIntersection (ZMod q) (((L.pull π₀ hπ₀).pull b' hb').B.pull i) 1 := by
    refine topSelf_of_cls_eq ?_ Z i (ZMod q)
    exact (GlobalTheory.CechPic.cls_pull L.isLB (b' ≫ π₀) _).trans ((GlobalTheory.CechPic.pull_comp b' π₀ _).trans
      ((congrArg (fun c => GlobalTheory.CechPic.pull b' c) (GlobalTheory.CechPic.cls_pull L.isLB π₀ (LB.isLB_pull L.isLB π₀)).symm).trans
        (GlobalTheory.CechPic.cls_pull (LB.isLB_pull L.isLB π₀) b' _).symm))
  have E := topSelf_of_cls_eq hcl Z i (ZMod q)
  rw [topSelf_pow hp _ _ Z i (ZMod q) hd, topSelf_pow hp _ _ Z i (ZMod q) hd, topSelf_pow hp _ _ Z i (ZMod q) hd,
    topSelf_pow hp _ _ Z i (ZMod q) hd] at E
  rw [topSelf_of_cls_eq_add hp (((W.amp.pull a ha).pow (b none).toNat).tens
      ((ArInt.comb (fun x => (W.root (FlagAr.setB O.Y B) x).pull a ha) fun x => b (some x)).pow W.k)).isLB
      ((W.amp.pull a ha).pow (b none).toNat).isLB
      ((ArInt.comb (fun x => (W.root (FlagAr.setB O.Y B) x).pull a ha) fun x => b (some x)).pow W.k).isLB
      (cls_tens _ _ _) Z i (ZMod q) hd,
    topSelf_pow hp _ _ Z i (ZMod q) hd, topSelf_pow hp _ _ Z i (ZMod q) hd, topSelf_comb hp _ _ Z i (ZMod q) hd] at E
  have E' : ((m' : ℕ) : ℝ) * (((W.k * m : ℕ) : ℝ) * (topSelfIntersection (ZMod q) (((L.pull π₀ hπ₀).pull b' hb').B.pull i) 1 : ℝ)) =
      (m' : ℝ) * ((k : ℕ) * ((((b none).toNat : ℕ) : ℝ) * (topSelfIntersection (ZMod q) ((W.amp.pull a ha).B.pull i) 1 : ℝ) +
        (W.k : ℝ) * ∑ x, (b (some x) : ℝ) * (topSelfIntersection (ZMod q) (((W.root (FlagAr.setB O.Y B) x).pull a ha).B.pull i) 1 : ℝ))) := by
    exact_mod_cast E
  rw [hc] at E'
  have hsum : ∑ x, (b (some x) : ℝ) * (topSelfIntersection (ZMod q) (((W.root (FlagAr.setB O.Y B) x).pull a ha).B.pull i) 1 : ℝ) =
      (m : ℝ) * ((O.Mb B u s c).n : ℕ) * ∑ x, -(A.sh u s x.1 x.2) *
        (topSelfIntersection (ZMod q) (((W.root (FlagAr.setB O.Y B) x).pull a ha).B.pull i) 1 : ℝ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by rw [← hbx x]; ring
  rw [hsum] at E'
  have hm'0 : (0 : ℝ) < (m' : ℕ) := Nat.cast_pos.2 hm'
  have key := mul_left_cancel₀ hm'0.ne' E'
  rw [e0]
  push_cast at key
  generalize (topSelfIntersection (ZMod q) (((L.pull π₀ hπ₀).pull b' hb').B.pull i) 1 : ℝ) = dL at key ⊢
  generalize (topSelfIntersection (ZMod q) ((W.amp.pull a ha).B.pull i) 1 : ℝ) = dA at key ⊢
  generalize (∑ x, -(A.sh u s x.1 x.2) *
    (topSelfIntersection (ZMod q) (((W.root (FlagAr.setB O.Y B) x).pull a ha).B.pull i) 1 : ℝ)) = S at key ⊢
  have hWm : (W.k : ℝ) * m ≠ 0 := by positivity
  have hdL : dL = (k : ℕ) * ((b none : ℝ) * dA + W.k * (m * ((O.Mb B u s c).n : ℕ) * S)) / (W.k * m) := by
    rw [eq_div_iff hWm]
    linear_combination key
  rw [hdL]
  field_simp

end GlobalTheory.NefDeRhamCover
