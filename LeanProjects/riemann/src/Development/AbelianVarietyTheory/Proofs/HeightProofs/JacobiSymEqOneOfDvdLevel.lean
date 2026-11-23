import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
import Formalism.LocalToGlobal.ProjectiveLattices.LevelPb
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLevelMulSplit
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsDeltaDatumHigherLevel
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLatticeEmbeddingLiftDatumHermitianSpace
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModuliSchemePolarizedAbelianLevel
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FunctionFieldAlgClosedLevelStatement

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.FinalJoin GlobalTheory.CompRat
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinalJoin.Cover

theorem zeta_mul_mem (F : IntermediateField ℚ ℂ) {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (h : n.Coprime m)
    (h1 : zeta m ∈ F) (h2 : zeta n ∈ F) : zeta (m * n) ∈ F := by
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 h
  have huv' : (u : ℂ) * n + v * m = 1 := by exact_mod_cast huv
  have hm' : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have e : zeta (m * n) = zeta m ^ u * zeta n ^ v := by
    unfold zeta
    rw [← Complex.exp_int_mul, ← Complex.exp_int_mul, ← Complex.exp_add]
    congr 1
    push_cast
    field_simp
    linear_combination (-1 : ℂ) * huv'
  rw [e]
  exact mul_mem (zpow_mem h1 u) (zpow_mem h2 v)

theorem FO_le_coeff {D : D7} (Q : Par D) (h : Q.PinField) : FO D ≤ Q.c.F := by
  rw [FO, IntermediateField.adjoin_le_iff]
  rintro _ ⟨y, rfl⟩
  have e := h (Q.eO.symm y)
  rw [RingEquiv.apply_symm_apply] at e
  have e' : D.what₂.phiO y = ((Q.eO.symm y : Q.c.F) : ℂ) := e
  rw [e']
  exact SetLike.coe_mem _

theorem half_of_split (D : D7) {p : ℕ} (hp : SplitOK D p) (P : HeightOneSpectrum (𝓞 D.host.K))
    (hP : ((p : ℕ) : 𝓞 D.host.K) ∈ P.asIdeal) (I : Ideal (𝓞 D.host.E))
    (hI : I = P.asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))) :
    I = Ideal.span {a | a ∈ I ∧ a ∈ Algebra.adjoin ℤ {w0E D}} ∧
      I * I.map (bH D) = Ideal.span {(p : 𝓞 D.host.E)} ∧ I ⊔ I.map (bH D) = ⊤ := by
  obtain ⟨e, he1, he2, hpb⟩ := LPb.pb_eq_JK D hp P hP
  rw [hpb, LPb.map_JK] at hI
  subst hI
  refine ⟨fromK_of_gen ⟨_, rfl, ?_⟩, ?_, ?_⟩
  · rintro y (rfl | hy)
    · exact Subalgebra.natCast_mem _ _
    · rw [Set.mem_singleton_iff.1 hy]
      exact Subalgebra.sub_mem _ (Algebra.subset_adjoin (Set.mem_singleton _)) (Subalgebra.intCast_mem _ _)
  · rw [LPb.QE_map_bar, LPb.QE_mul D _ _ he1 he2]
  · rw [LPb.QE_map_bar, ← Ideal.isCoprime_iff_sup_eq]
    exact LPb.QE_cop_self D _ _ he2

theorem exists_cover : ∀ (D : D7) (Q : Par D), Q.Pins → Q.Canon → ∀ p : ℕ, FieldOK D p → jacobiSym (-(D.host.d : ℤ)) p = 1 → ∀ (P : HeightOneSpectrum (𝓞 D.host.K)), ((p : ℕ) : 𝓞 D.host.K) ∈ P.asIdeal → p.Prime ∧ 5 ≤ p ∧ ∀ j, InR D j → ∃ d : DeltaDat (Q.Xo j) Q.c 0, CoverOK d p (P.asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))) ∧ FnAlgClosed d.Xo₂ d.c₂ := by
  intro D Q hP hC p hK hj P hPp
  have hpp : p.Prime ∧ p % 15 = 1 ∧ ∀ i, p ≠ D.host.g i := by
    rcases hK.own with rfl | rfl
    · exact ⟨D.host.pde_prime, D.host.pde_mod.1, fun i => (D.host.pde_ne_g i).1⟩
    · exact ⟨D.host.pde'_prime, D.host.pde_mod.2, fun i => (D.host.pde_ne_g i).2⟩
  obtain ⟨hp, h15, hg⟩ := hpp
  have h5 : 5 ≤ p := by have := hp.two_le; omega
  refine ⟨hp, h5, fun j hjR => ?_⟩
  have hM : Q.l.M = D.host.g 0 * D.host.g 1 := hP.2.1.1
  have hA : Q.l.A = 1 := hP.2.1.2
  have hcop : p.Coprime Q.l.M := by
    rw [hM]
    exact Nat.Coprime.mul_right ((Nat.coprime_primes hp (D.host.g_prime 0)).2 (hg 0))
      ((Nat.coprime_primes hp (D.host.g_prime 1)).2 (hg 1))
  obtain ⟨h1, h2, h3⟩ := half_of_split D ⟨hp, by omega, hj⟩ P hPp _ rfl
  have hw : Q.H.w0 = w0E D := by rw [hC.1]; rfl
  have hb : (Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) = bH D := by rw [hC.1]; rfl
  rw [← hw] at h1
  rw [← hb] at h2 h3
  obtain ⟨l₂, hd, hM₂, hMb, hA₂⟩ := (GlobalTheory.exists_level_mul_split _ Q.H Q.l).1 p _
    (hp.odd_of_ne_two (by omega)) hcop h1 h2 h3
  obtain ⟨-, hr, -, -⟩ := GlobalTheory.Member.exists_iotaOK D Q hP j hjR
  have hr1 : 1 ≤ (Q.Dw j).p + (Q.Dw j).q := by
    have h1 := D.R.two_le_m; have h2 := D.R.m_add_three_le_k
    rw [hr]; unfold Ranks.r; omega
  obtain ⟨Xo₂⟩ := GlobalTheory.Moduli.moduli_scheme_exists _ Q.H (Q.Dw j) l₂ hr1
  have hz : zeta Q.l.M ∈ Q.c.F := by
    have := Q.c.zeta_mem
    rwa [Level.M', hA, Nat.lcm_one_right] at this
  let c₂ : Coeff l₂ :=
    { F := Q.c.F
      fin := Q.c.fin
      conj := Q.c.conj
      zeta_mem := by
        rw [Level.M', hA₂, hA, Nat.lcm_one_right, hM₂]
        exact zeta_mul_mem _ (by have := Q.l.three_le; omega) hp.pos hcop hz (FO_le_coeff Q hP.2.2.1 hK.zetaP)
      le := by
        have := Q.c.le
        unfold KA at this ⊢
        rwa [hA₂] }
  obtain ⟨d, e1, e2, e3, -, -, -, hlev, hnab⟩ := GlobalTheory.LevelCover.exists_deltaDat_isLev _ Q.H (Q.Dw j) Q.l (Q.Xo j) Q.c
    hr1 0 p _ l₂ Xo₂ c₂ rfl hd hM₂ hcop hMb h3
  have hA' : d.l₂.A = 1 := by rw [e3, hA₂, hA]
  refine ⟨d, ⟨e1, e2, hlev, hA', hnab⟩, ?_⟩
  refine GlobalTheory.T.function_field_alg_closed_level D Q hP hC (D.host.g 0 * D.host.g 1 * p)
    (Nat.mul_pos (Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos) hp.pos) hK.curve j hjR d.l₂ d.Xo₂ d.c₂
    hA' ?_ d.hF
  rw [e3, hM₂, hM]

theorem exists_cover_of_fieldOK : ∀ (D : D7) (Q : Par D), Q.Pins → Q.Canon → ∀ p : ℕ, FieldOK D p → ∀ (P : HeightOneSpectrum (𝓞 D.host.K)), ((p : ℕ) : 𝓞 D.host.K) ∈ P.asIdeal → p.Prime ∧ 5 ≤ p ∧ ∀ j, InR D j → ∃ d : DeltaDat (Q.Xo j) Q.c 0, CoverOK d p (P.asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))) ∧ FnAlgClosed d.Xo₂ d.c₂ := by
  intro D Q hP hC p hK
  refine exists_cover D Q hP hC p hK ?_
  have h : D.host.cls p = PrimeClass.splitK := hK.split
  exact ((Formalism.BasicNotions.primeClass_eq_splitK_iff D.host.toHostRaw).1 h).2.2.2

end GlobalTheory.FinalJoin.Cover
