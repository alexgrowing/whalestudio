import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsInvOne
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CongruenceLevelEqDepthSucc
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PhiTopTargetTwist
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.TopRowsQ

open GlobalTheory.TopStep GlobalTheory.Mem.Col2 GlobalTheory.TopLaw

theorem redV_eq_of_cong {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {P : HeightOneSpectrum (𝓞 E)} {c : ℕ}
    (hc : 0 < c) {a b : Sp E n} (hb : b ∈ stdAt E n P) (h : (((qOf P : ℕ) : E) ^ c)⁻¹ • (a - b) ∈ stdAt E n P) :
    a ∈ stdAt E n P ∧ redV P a = redV P b := by
  have hq := qOf_ne_zero (P := P)
  have h1 : ∀ i, IntAt P ((((qOf P : ℕ) : E) ^ c)⁻¹ * (a i - b i)) := fun i => mem_stdAt.1 h i
  have h2 : ∀ i, IntAt P (a i - b i) := fun i => by
    have h3 := (intAt_pow (intAt_nat (P := P) (qOf P)) c).mul (h1 i)
    convert h3 using 1
    field_simp
  have ha : ∀ i, IntAt P (a i) := fun i => by
    have h3 := (h2 i).add (mem_stdAt.1 hb i)
    convert h3 using 1
    ring
  refine ⟨mem_stdAt.2 ha, funext fun i => ?_⟩
  have h4 : redP P (a i - b i) = 0 := by
    apply redP_eq_zero_of_div
    have h3 := (intAt_pow (intAt_nat (P := P) (qOf P)) (c - 1)).mul (h1 i)
    convert h3 using 1
    obtain ⟨c, rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
    simp only [Nat.add_sub_cancel, pow_succ]
    field_simp
  rw [reduction_sub (ha i) (mem_stdAt.1 hb i), sub_eq_zero] at h4
  exact h4

theorem lamQB_mul_levCong : ∀ {X : Fields} {R : Ranks} (ξ : Chr X.F X.E X.K) (Q : Finset (HeightOneSpectrum (𝓞 X.E))) (P : Q) (c M : ℕ), 1 ≤ M →
    ∀ (k : Formalism.L2.Col.GLint X.E (R.N R.m) P.1) (hk : k ∈ (levCong (N_m_succ R) P.1 c (rowTyQ R ξ Q P)).H)
    (g : Sp X.E (R.N R.m) ≃ₗ[X.E] Sp X.E (R.N R.m)) (g'' : Sp X.E ((R.N R.m - 1) + 0) ≃ₗ[X.E] Sp X.E ((R.N R.m - 1) + 0)),
    g'' ∈ LocE.JQ P.1 (qOf P.1) R.r (R.N R.m - 1) 0 →
    prXpG X.E (R.N R.m) ∘ₗ g.toLinearMap = g''.toLinearMap ∘ₗ prXpG X.E (R.N R.m) →
    CongE P.1 (2 * M) g (k⁻¹).1 →
    LocE.lamQB (resChar ξ P.1) R.r (R.N R.m - 1) g''.toLinearMap *
      (((levCong (N_m_succ R) P.1 c (rowTyQ R ξ Q P)).lam ⟨k, hk⟩ : X.Kˣ) : X.K) = 1 := by
  intro X R ξ Q P c M hM k hk g g'' hJ hpr hC
  have hN := N_m_succ R
  obtain ⟨j, hj, hb⟩ := (mem_levCong (N_m_succ R) c _ k).1 hk
  rw [levCong_lam (N_m_succ R) c _ hk hj hb, levRed_lam]
  have ek : redGL _ P.1 k = diagEmb _ (by omega : R.N R.m - 1 ≤ R.N R.m) (redGL _ P.1 j) := by
    have e := redGL_of_prinCong c.succ_pos hb
    rw [map_mul, map_inv, inv_mul_eq_one, redGL_extI] at e
    exact e.symm
  let g2 : Formalism.L2.Col.GLint X.E (R.N R.m - 1) P.1 := ⟨g'', hJ.1⟩
  have hred : redGL _ P.1 g2 = (redGL _ P.1 j)⁻¹ := by
    refine redGL_eq g2 fun x hx => ?_
    let v : Sp X.E (R.N R.m) := fun l => if h : l.1 < R.N R.m - 1 then x ⟨l.1, h⟩ else 0
    have hv : v ∈ stdAt X.E (R.N R.m) P.1 := mem_stdAt.2 fun l => by
      by_cases h : l.1 < R.N R.m - 1
      · simp only [v, dif_pos h]; exact mem_stdAt.1 hx _
      · simp only [v, dif_neg h]; simpa using intAt_nat (P := P.1) 0
    have hpv : prXpG X.E (R.N R.m) v = x := by
      funext i
      show v _ = x i
      simp only [v, dif_pos (show i.1 < R.N R.m - 1 from i.2)]
      rfl
    have hxg : g'' x = prXpG X.E (R.N R.m) (g v) := by
      have := LinearMap.congr_fun hpr v
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hpv] at this
      exact this.symm
    obtain ⟨-, e1⟩ := redV_eq_of_cong (by omega : 0 < 2 * M) (glint_mem k⁻¹ hv) (hC v hv)
    have e2 := redV_redGL k⁻¹ hv
    rw [map_inv, ek, ← map_inv, diagEmb_val] at e2
    funext i
    have e3 := congrFun e1 (Br.iC hN i)
    rw [e2, (diagMat_mulVec hN _ _).1] at e3
    show redP P.1 (g'' x i) = _
    rw [hxg]
    refine e3.trans ?_
    congr 1
    funext l
    show redP P.1 (v (Br.iC hN l)) = redP P.1 (x l)
    simp only [v, Br.iC, dif_pos l.2]
  have hH : redGL _ P.1 g2 ∈ HQ (𝓞 X.E ⧸ P.1.asIdeal) (R.N R.m - 1) R.r (R.m * R.t) := hred ▸ inv_mem hj
  have hl := lamQB_eq_red (resChar ξ P.1) (rank_X'_eq R) g2 hH
  rw [show (g''.toLinearMap : HomE X.E _ _) = g2.1.toLinearMap from rfl, hl]
  have e4 : lamQ (resChar ξ P.1) _ R.r (R.m * R.t) ⟨redGL _ P.1 g2, hH⟩ =
      (lamQ (resChar ξ P.1) _ R.r (R.m * R.t) ⟨redGL _ P.1 j, hj⟩)⁻¹ := by
    rw [← map_inv]
    exact congrArg _ (Subtype.ext hred)
  rw [← Units.val_mul, e4]
  show (((_ : X.Kˣ)⁻¹)⁻¹ * (lamQP ξ P.1 (R.N R.m - 1) R.r (R.m * R.t) ⟨redGL _ P.1 j, hj⟩)⁻¹ : X.Kˣ).1 = 1
  rw [inv_inv, lamQP, mul_inv_cancel, Units.val_one]

end GlobalTheory.TopRowsQ
