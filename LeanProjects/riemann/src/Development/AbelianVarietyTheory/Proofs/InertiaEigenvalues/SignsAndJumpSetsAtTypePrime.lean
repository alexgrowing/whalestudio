import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.AdmissibleParameterJ
import Formalism.SharpRestriction.LevelLetterCocycles.PairedCharacterCondition
import Formalism.LocalToGlobal.LatticeGeometry.CmTypeMeetsConjugatePair
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqOfStabilizerTrivial
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InducesWAndExistsEmb
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

noncomputable section

namespace GlobalTheory.HostJumpSets

open AdmissibleParameterJ

variable {D : D7}

theorem Jp_finite (j : ℕ) (ρ : D.what₂.Tau) : (Jp D j ρ).Finite := by
  refine (((Set.finite_range fun a : Fin (D.R.k - 1) => sz D j ρ + (D.hc ρ).v a + c0 D).union
    (Set.finite_range fun a : Fin D.R.m => sz D j ρ - (D.hc ρ).b a + c0 D)).union
    (Set.finite_range fun c : Fin D.R.t => ((c : ℕ) : ℚ))).subset ?_
  rintro q ((⟨a, rfl⟩ | ⟨a, rfl⟩) | ⟨c, hc, rfl⟩)
  · exact Or.inl (Or.inl ⟨a, rfl⟩)
  · exact Or.inl (Or.inr ⟨a, rfl⟩)
  · exact Or.inr ⟨⟨c, hc⟩, rfl⟩

theorem refl_injective : Function.Injective (AdmissibleParameterJ.refl D) := by
  intro x y h
  simp only [AdmissibleParameterJ.refl] at h
  linarith

theorem refl_surjective : Function.Surjective (AdmissibleParameterJ.refl D) := by
  intro y
  refine ⟨((D.R.t : ℚ) - 1) - y, ?_⟩
  simp only [AdmissibleParameterJ.refl]
  ring

theorem JJ_finite (up : Bool) (j : ℕ) (ρ : D.what₂.Tau) : (JJ D up j ρ).Finite := by
  cases up
  · exact (Jp_finite j ρ).preimage refl_injective.injOn
  · exact Jp_finite j ρ

theorem JJ_ncard (up : Bool) (j : ℕ) (ρ : D.what₂.Tau) : (JJ D up j ρ).ncard = (Jp D j ρ).ncard := by
  cases up
  · exact Set.ncard_preimage_of_injective_subset_range refl_injective
      (fun q _ => refl_surjective q)
  · rfl

theorem abs_le_two_b (L : SizeData₂ D) (hJe : JumpAbsoluteBound L) {j : ℕ} (hj1 : 1 ≤ j) (hj2 : j ≤ D.R.m)
    (ρ : D.what₂.Tau) (up : Bool) (q : ℚ) (hq : q ∈ JJ D up j ρ) : |(q : ℝ)| ≤ 2 * L.sc.b :=
  ((hJe.1 j hj1 hj2 ρ up q hq).trans hJe.2.1).trans hJe.2.2.2

theorem elem_ok (L : SizeData₂ D) (hJb : CloudCentreDistance L) (hJc : jcCondition L) (hJe : JumpAbsoluteBound L)
    {j : ℕ} (hj1 : 1 ≤ j) (hj2 : j ≤ D.R.m) (ρ : D.what₂.Tau)
    (up : Bool) (a : ℤ) (ha : (a : ℚ) ∈ JJ D up j ρ) :
    ((0 ≤ a ∧ a < D.R.t) ∨ |(a : ℚ) - PairedCharacterCondition.cen (D := D)| ≤ (⌊L.etaSz⌋₊ : ℚ) + 1 ∨
        PairedCharacterCondition.cloud (D := D) up (⌊3 * L.sc.b⌋₊ + 2 + 0) a) ∧ a ≠ -1 ∧ a ≠ D.R.t := by
  have hnot := (hJc j hj1 hj2 ρ).2.1 up
  refine ⟨?_, fun h => hnot.1 (by rw [h] at ha; exact_mod_cast ha),
    fun h => hnot.2 (by rw [h] at ha; exact_mod_cast ha)⟩
  have hfl : 3 * L.sc.b < (⌊3 * L.sc.b⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hfe : L.etaSz < (⌊L.etaSz⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _

  have hcl : ∀ q ∈ cloudJ D j ρ, (D.R.t : ℚ) + 1 < q ∧ q ≤ ((⌊3 * L.sc.b⌋₊ + 2 + 0 : ℕ) : ℚ) := by
    intro q hq
    refine ⟨(hJc j hj1 hj2 ρ).2.2.1 q hq, ?_⟩
    have h2 := abs_le_two_b L hJe hj1 hj2 ρ true q (Or.inl (Or.inl hq))
    have h3 : (q : ℝ) ≤ ((⌊3 * L.sc.b⌋₊ + 2 + 0 : ℕ) : ℝ) := by
      push_cast
      linarith [le_abs_self (q : ℝ)]
    exact_mod_cast h3
  have hlow : ∀ q ∈ lowJ D j ρ, |q - c0 D| ≤ (⌊L.etaSz⌋₊ : ℚ) + 1 := by
    intro q hq
    have h1 := (hJb j hj1 hj2 ρ).2.1 q hq
    have h2 : ((|q - c0 D| : ℚ) : ℝ) ≤ (((⌊L.etaSz⌋₊ : ℚ) + 1 : ℚ) : ℝ) := by
      push_cast at h1 ⊢
      linarith
    exact_mod_cast h2
  cases up
  ·
    change AdmissibleParameterJ.refl D (a : ℚ) ∈ Jp D j ρ at ha
    rcases ha with (hq | hq) | ⟨c, hc, hx⟩
    · right; right
      obtain ⟨h1, h2⟩ := hcl _ hq
      simp only [PairedCharacterCondition.cloud, PairedCharacterCondition.cen, AdmissibleParameterJ.refl] at h1 h2 ⊢
      simp only [Bool.false_eq_true, if_false]
      constructor <;> linarith
    · right; left
      have h := hlow _ hq
      simp only [PairedCharacterCondition.cen, AdmissibleParameterJ.refl, c0] at h ⊢
      rw [show (a : ℚ) - ((D.R.t : ℚ) - 1) / 2 = -((D.R.t : ℚ) - 1 - (a : ℚ) - ((D.R.t : ℚ) - 1) / 2) by ring,
        abs_neg]
      exact h
    · left
      simp only [AdmissibleParameterJ.refl] at hx
      have hx' : (a : ℚ) = ((D.R.t : ℤ) - 1 - (c : ℤ) : ℤ) := by push_cast; linarith
      have hx'' : a = (D.R.t : ℤ) - 1 - c := by exact_mod_cast hx'
      omega
  · change (a : ℚ) ∈ Jp D j ρ at ha
    rcases ha with (hq | hq) | ⟨c, hc, hx⟩
    · right; right
      obtain ⟨h1, h2⟩ := hcl _ hq
      simp only [PairedCharacterCondition.cloud, PairedCharacterCondition.cen, if_true]
      constructor <;> linarith
    · right; left
      exact hlow _ hq
    · left
      have hx'' : a = c := by exact_mod_cast hx
      omega

theorem algHom_eq_of_finrank_one {F K A : Type} [Field F] [Field K] [Ring A] [Algebra F K] [Algebra F A]
    (h : finrank F K = 1) (f g : K →ₐ[F] A) : f = g := by
  ext x
  have hx : x ∈ (⊥ : Subalgebra F K) := by
    rw [Subalgebra.bot_eq_top_of_finrank_eq_one h]; trivial
  obtain ⟨c, rfl⟩ := Algebra.mem_bot.1 hx
  simp

theorem emb_inj (D : D7) : Function.Injective D.host.emb := by
  intro g g' h
  have h1 : D.host.sigmaOf g = D.host.sigmaOf g' :=
    AlgEquiv.ext fun x => D.host.φ₀.injective (RingHom.congr_fun h x)
  exact (D.host.gal).symm.injective h1

theorem decide_flip {P Q : Prop} {iP : Decidable P} {iQ : Decidable Q} (h : P ↔ ¬ Q) :
    @decide P iP = !@decide Q iQ := by
  by_cases hq : Q
  · rw [decide_eq_true hq, decide_eq_false (fun hp => h.1 hp hq)]; rfl
  · rw [decide_eq_false hq, decide_eq_true (h.2 hq)]; rfl

theorem typeU_flip (D : D7) (ep : Bool) (g : D.R.GG) :
    TypeU D ep g ↔ ¬ TypeU D ep (g * D.R.cc) := by
  have hP := Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem g
  unfold TypeU
  cases ep <;> by_cases h : g ∈ D.R.Psi <;> simp_all

def incl (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) :
    Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1 :=
  ((D.nbr i w hw).Kw.1.val).codRestrict (D.nbr i w hw).LL.1.toSubalgebra
    (fun x => (D.nbr i w hw).LL_split (D.nbr i w hw).Kw.1.val x)

end GlobalTheory.HostJumpSets

end

noncomputable section

namespace GlobalTheory.HostJumpSets

open AdmissibleParameterJ

theorem main : ∀ (D : D7) (L : SizeData₂ D) (ep : Bool), AdmissibleParameterJ.hodgeTateJumpsAtModulesForSign D ep → AdmissibleParameterJ.CloudCentreDistance L → AdmissibleParameterJ.jcCondition L → AdmissibleParameterJ.JumpAbsoluteBound L → (D.R.t : ℝ) ≤ L.sc.b → ∀ (i : D.nd.Loc) (k : Fin 2) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), D.nd.l i = D.host.g k → GoodR D.nd i r → ∃ (sg : HeightOneSpectrum (𝓞 D.host.E) → Bool) (U : HeightOneSpectrum (𝓞 D.host.E) → Finset ℤ), PairedCharacterCondition.SignOK i sg ∧ PairedCharacterCondition.HostJ i r ⌊L.etaSz⌋₊ (⌊3 * L.sc.b⌋₊ + 2) 0 sg U := by
  intro D L ep hJa hJb hJc hJe _htb i k r hk hgood
  obtain ⟨hdeg, hemb⟩ := GlobalTheory.TypePlace.type_prime_places D i k hk
  have hj := D.nd.j_range i
  have hex := fun w (hw : w ∈ placesOver D.host.E (D.nd.l i)) =>
    hJa i r hgood w hw (TruncatedSeriesCountingIdentities.CoefExt.self i w hw) (incl D i w hw)
  choose gf ρf hR hJ using hex
  classical
  let sg : HeightOneSpectrum (𝓞 D.host.E) → Bool := fun w =>
    if hw : w ∈ placesOver D.host.E (D.nd.l i) then decide (TypeU D ep (gf w hw)) else false
  let U : HeightOneSpectrum (𝓞 D.host.E) → Finset ℤ := fun w =>
    if hw : w ∈ placesOver D.host.E (D.nd.l i) then
      (Finset.Icc (-((⌊3 * L.sc.b⌋₊ + 2 : ℕ) : ℤ)) ((⌊3 * L.sc.b⌋₊ + 2 : ℕ) : ℤ)).filter
        (fun a : ℤ => (a : ℚ) ∈ JJ D (sg w) (D.nd.j i) (ρf w hw))
    else ∅
  have hsg : ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)), sg w = decide (TypeU D ep (gf w hw)) :=
    fun w hw => dif_pos hw
  refine ⟨sg, U, ?_, ?_⟩
  · intro w w' hw hc _hne
    have hw' : w' ∈ placesOver D.host.E (D.nd.l i) := by
      have := hc ((D.nd.l i : ℕ) : 𝓞 D.host.E) ((D.nd.l i : ℕ) : 𝓞 D.host.E) (by simp)
      exact this.1 hw
    have hind : ∀ v (hv : v ∈ placesOver D.host.E (D.nd.l i)),
        InducesW D.nd i (gEmb (TruncatedSeriesCountingIdentities.CoefExt.self i v hv) (incl D i v hv)) v := fun v hv =>
      (GlobalTheory.LocalEmbedding.inducesW_and_exists_emb D i v hv _ (incl D i v hv) _ (fun _ => rfl)).1
    have heq : gEmb (TruncatedSeriesCountingIdentities.CoefExt.self i w hw) (incl D i w hw) =
        (gEmb (TruncatedSeriesCountingIdentities.CoefExt.self i w' hw') (incl D i w' hw')).comp (D.host.conj : D.host.E →+* D.host.E) := by
      apply hemb
      intro x
      let X : 𝓞 D.host.E := ⟨(D.host.conj : D.host.E →+* D.host.E) (x : D.host.E),
        (RingOfIntegers.isIntegral_coe x).map (D.host.conj : D.host.E →+* D.host.E).toIntAlgHom⟩
      rw [hind w hw x, RingHom.comp_apply]
      have h2 := hind w' hw' X
      rw [show ((X : 𝓞 D.host.E) : D.host.E) = (D.host.conj : D.host.E →+* D.host.E) (x : D.host.E) from rfl] at h2
      rw [h2]
      exact hc x X rfl
    have hg : gf w hw = gf w' hw' * D.R.cc := by
      apply emb_inj D
      rw [Formalism.L2.Geo.emb_mul_cc_comp, ← (hR w hw).1, ← (hR w' hw').1, heq]
      rfl
    rw [hsg w hw, hsg w' hw', hg]
    exact decide_flip (typeU_flip D ep (gf w' hw'))
  · intro w hw
    have hU : U w = (Finset.Icc (-((⌊3 * L.sc.b⌋₊ + 2 : ℕ) : ℤ)) ((⌊3 * L.sc.b⌋₊ + 2 : ℕ) : ℤ)).filter
        (fun a : ℤ => (a : ℚ) ∈ JJ D (sg w) (D.nd.j i) (ρf w hw)) := dif_pos hw
    refine ⟨?_, ?_, ?_⟩
    · rw [hU, ← Set.ncard_coe_finset]
      have h1 : ((Finset.filter (fun a : ℤ => (a : ℚ) ∈ JJ D (sg w) (D.nd.j i) (ρf w hw))
          (Finset.Icc (-((⌊3 * L.sc.b⌋₊ + 2 : ℕ) : ℤ)) ((⌊3 * L.sc.b⌋₊ + 2 : ℕ) : ℤ)) : Finset ℤ) : Set ℤ).ncard ≤
          (JJ D (sg w) (D.nd.j i) (ρf w hw)).ncard :=
        Set.ncard_le_ncard_of_injOn (fun a : ℤ => (a : ℚ))
          (fun a ha => (Finset.mem_filter.1 (Finset.mem_coe.1 ha)).2)
          (fun a _ b _ h => Int.cast_injective h) (JJ_finite _ _ _)
      rw [JJ_ncard] at h1
      exact h1.trans_eq ((hJb _ hj.1 hj.2 (ρf w hw)).2.2.2.2.2)
    · intro x τ a ha
      obtain rfl : τ = incl D i w hw := algHom_eq_of_finrank_one (hdeg w hw).1 _ _
      have e : TruncatedSeriesCountingIdentities.locC (TruncatedSeriesCountingIdentities.CoefExt.self i w hw) (rTwO D.nd i r x) = Br.loc D.nbr i w hw (rTwO D.nd i r x) := by
        ext; rfl
      have h1 := ((hJ w hw).1 x a).1
      rw [e] at h1
      have hmem := h1.1 ha
      rw [← hsg w hw] at hmem
      rw [hU, Finset.mem_filter, Finset.mem_Icc]
      refine ⟨?_, hmem⟩
      have hb := abs_le_two_b L hJe hj.1 hj.2 (ρf w hw) _ _ hmem
      have hfl : 3 * L.sc.b < (⌊3 * L.sc.b⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
      have h0 : 0 ≤ L.sc.b := by linarith [abs_nonneg ((a : ℚ) : ℝ)]
      rw [abs_le] at hb
      push_cast at hb
      have h3 : (a : ℝ) ≤ ((⌊3 * L.sc.b⌋₊ + 2 : ℕ) : ℝ) := by push_cast; linarith
      have h4 : -((⌊3 * L.sc.b⌋₊ + 2 : ℕ) : ℝ) ≤ (a : ℝ) := by push_cast; linarith
      constructor
      · exact_mod_cast h4
      · exact_mod_cast h3
    · intro a ha
      rw [hU, Finset.mem_filter] at ha
      exact elem_ok L hJb hJc hJe hj.1 hj.2 (ρf w hw) (sg w) a ha.2

end GlobalTheory.HostJumpSets

end
