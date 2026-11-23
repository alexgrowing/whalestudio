import Formalism.PeriodIntegrals.HasseOrdBd

noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps

namespace PI.HasseOrdBdW

def wi {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO))
    {N : ℕ} {wL : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL) : Lc X la w := w0inv X la w

def S1 : Prop :=
  ∀ {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO))
    {N : ℕ} {wL : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL) (T : ℕ) (β : Idx D j N →₀ ℕ),
    ∃ m : ℤ, (m ≠ 0 → ∑ k, β (0, k) = β.sum fun _ n => n) ∧
      hasse X la w β (wi X la w ^ T) =
        (m : Lc X la w) * algebraMap (Rp X la N) (Lc X la w) (∏ k, emb X la N (X.inc wL (w k)) ^ β (0, k)) *
          wi X la w ^ (T + β.sum fun _ n => n)

def S2 : Prop :=
  ∀ {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO))
    (y : X.Pt la) {N : ℕ} {wL wF : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL) (d : ℝ),
    (∀ k, (d : EReal) ≤ X.vAt la y (X.inc wL (w k))) →
    ∀ (m : ℕ) (g : B.Cusp j (addL wF wL m)) (e : Fin N → ℕ) (n : ℕ), ∑ k, e k = n →
    ∃ g' : B.Cusp j (addL wF wL (m + n)),
      X.inc _ g * ∏ k, X.inc wL (w k) ^ e k = X.inc _ g' ∧
      X.vAt la y (X.inc _ g) + (((n : ℝ) * d : ℝ) : EReal) ≤ X.vAt la y (X.inc _ g')

def S3 : Prop :=
  ∀ {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (Q : LocalPointData G la),
    PublishedIntClos → Q.InCurve → ∀ ζ : PtsG G la,
      Q.ordA ζ 0 = ⊤ ∧ ∀ (m : ℤ) (v : SectionSheafQuotient X la G.w wF), Q.ordA ζ v ≤ Q.ordA ζ (m • v)

def S4 : Prop :=
  ∀ (e : ℕ) (vf vg : EReal) (d : ℝ) (T n : ℕ), vf ≠ ⊥ → vf + (((n : ℝ) * d : ℝ) : EReal) ≤ vg →
    (e : EReal) * (vf - (T : EReal) * (d : EReal)) ≤ (e : EReal) * (vg - ((T + n : ℕ) : EReal) * (d : EReal))

theorem toE_mono {a b : WithTop ℤ} (h : a ≤ b) : toE a ≤ toE b := by
  induction b using WithTop.recTopCoe with
  | top => simp [toE]
  | coe b =>
    induction a using WithTop.recTopCoe with
    | top => simp at h
    | coe a =>
      simp only [toE]
      exact_mod_cast WithTop.coe_le_coe.mp h

theorem hasseOrdBd_of (h1 : S1) (h2 : S2) (h3 : S3) (h4 : S4) : PI.HasseOrdBd := by
  intro D B P j X ka wL wF G la Q S T hPIC hC hTie hW f β hβ hx ζ
  obtain ⟨hdT, hdB, -, -, -, -, hT⟩ := hTie ζ
  obtain ⟨h30, h3m⟩ := h3 G la Q hPIC hC ζ
  set d := (X.depth S.sW wL la (Q.y ζ)).toReal with hd_def
  have hd : X.depth S.sW wL la (Q.y ζ) = (d : EReal) := (EReal.coe_toReal hdT hdB).symm
  obtain ⟨m, hmn, hform⟩ := h1 X la G.w T β
  have e1 : (frac X la G.w T (emb X la G.N (X.inc _ f)) : Lc X la G.w) =
      algebraMap (Rp X la G.N) (Lc X la G.w) (bcV X la G.N (X.bc la (X.inc _ f))) * wi X la G.w ^ T := rfl
  have key : hasse X la G.w β (frac X la G.w T (emb X la G.N (X.inc _ f))) =
      (m : Lc X la G.w) * (algebraMap (Rp X la G.N) (Lc X la G.w)
        (emb X la G.N (X.inc _ f) * ∏ k, emb X la G.N (X.inc wL (G.w k)) ^ β (0, k)) *
          wi X la G.w ^ (T + β.sum fun _ n => n)) := by
    rw [e1, hasse_bcV_mul, hform, map_mul, emb_eq_bcV]
    ring
  have main : ∀ z : ↥(HK X la G.w wF),
      (z : Lw X la G.w) = hasse X la G.w β (frac X la G.w T (emb X la G.N (X.inc _ f))) →
      (ep (unifO X la G.N) ζ : EReal) *
          (X.vAt la (Q.y ζ) (X.inc _ f) - (T : EReal) * X.depth S.sW wL la (Q.y ζ)) ≤
        toE (Q.ordA ζ (toA0K X la G.w wF z)) := by
    intro z hz
    by_cases hm : m = 0
    · have hz0 : z = 0 := by
        apply Subtype.ext
        have := hz.trans key
        rw [hm] at this
        simp only [Int.cast_zero, zero_mul] at this
        exact this
      rw [hz0, map_zero, h30]
      simp [toE]
    · have hn := hmn hm
      obtain ⟨g', hg', hv⟩ := h2 X la (Q.y ζ) G.w d
        (fun k => by rw [← hd]; exact iInf₂_le (G.w k) (hW k)) T f (fun k => β (0, k)) _ hn
      have hz' : z = m • toHK X la G.w wF (T + β.sum fun _ n => n)
          ⟨emb X la G.N (X.inc _ g'), emb_mem_Vw X la G.N _ g'⟩ := by
        apply Subtype.ext
        have h5 : ((m • toHK X la G.w wF (T + β.sum fun _ n => n)
            ⟨emb X la G.N (X.inc _ g'), emb_mem_Vw X la G.N _ g'⟩ : ↥(HK X la G.w wF)) : Lw X la G.w) =
            m • frac X la G.w (T + β.sum fun _ n => n) (emb X la G.N (X.inc _ g')) := by
          rw [AddSubgroupClass.coe_zsmul, coe_toHK]
        have h6 : algebraMap (Rp X la G.N) (Lc X la G.w)
            (emb X la G.N (X.inc _ f) * ∏ k, emb X la G.N (X.inc wL (G.w k)) ^ β (0, k)) =
            algebraMap (Rp X la G.N) (Lc X la G.w) (emb X la G.N (X.inc _ g')) := by
          rw [← hg']
          congr 1
          simp only [map_mul, map_prod, map_pow]
        have h7 : ((m : Lc X la G.w) * (algebraMap (Rp X la G.N) (Lc X la G.w) (emb X la G.N (X.inc _ g')) *
            wi X la G.w ^ (T + β.sum fun _ n => n)) : Lc X la G.w) =
            (m • frac X la G.w (T + β.sum fun _ n => n) (emb X la G.N (X.inc _ g')) : Lw X la G.w) := by
          rw [zsmul_eq_mul]
          rfl
        rw [h5]
        exact hz.trans (key.trans ((congrArg (fun t => (m : Lc X la G.w) * (t * wi X la G.w ^ (T + β.sum fun _ n => n))) h6).trans h7))
      have htie := hT (T + β.sum fun _ n => n) g'
      rw [hd] at htie ⊢
      rw [hz', map_zsmul]
      calc (ep (unifO X la G.N) ζ : EReal) * (X.vAt la (Q.y ζ) (X.inc _ f) - (T : EReal) * (d : EReal))
          ≤ (ep (unifO X la G.N) ζ : EReal) * (X.vAt la (Q.y ζ) (X.inc _ g') -
              ((T + β.sum fun _ n => n : ℕ) : EReal) * (d : EReal)) :=
            h4 _ _ _ d T _ (X.vAt_ne_bot la _ _) hv
        _ = toE (Q.ordA ζ (toA0K X la G.w wF (toHK X la G.w wF (T + β.sum fun _ n => n)
              ⟨emb X la G.N (X.inc _ g'), emb_mem_Vw X la G.N _ g'⟩))) := htie.symm
        _ ≤ _ := toE_mono (h3m m _)
  exact main _ rfl

end PI.HasseOrdBdW
