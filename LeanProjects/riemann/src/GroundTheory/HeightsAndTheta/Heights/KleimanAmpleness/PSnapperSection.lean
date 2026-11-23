import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SnapperSectionSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SnapperQuotAddSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SnapperQuotDevissageSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.MulQuotEqSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SectionNonvanishSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SectionMulInjSt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SnapperSectionObj
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistAlg
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSnapper
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PIdealTwistFamily
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCutZeroNotLe
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PStepThreeAway
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AssemblyBase
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

namespace SnapperSections

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem twistPows_sub (F : SubSystem k x Ω) : ∀ (t : ℕ) (L : Fin t → SubSystem k x Ω) (n : Fin t → ℕ)
    (I : Chart x), (F.twistPows t L n).sub I = F.sub I * ∏ j, (L j).sub I ^ n j
  | 0, _, _, I => by simp [SubSystem.twistPows]
  | t + 1, L, n, I => by
    rw [SubSystem.twistPows, SubSystem.twist_sub_eq_mul_of_line, SubSystem.pow_sub, twistPows_sub F t,
      Fin.prod_univ_castSucc]
    ring

def powsBundle (F : LineBundle k x) : (t : ℕ) → (Fin t → LineBundle k x) → (Fin t → ℕ) → LineBundle k x
  | 0, _, _ => F
  | t + 1, L, n => (powsBundle F t (fun j => L j.castSucc) (fun j => n j.castSucc)).tensorProd
      ((L (Fin.last t)).powBundle (n (Fin.last t)))

theorem tensorProd_sub (P Q : LineBundle k x) (I : Chart x) :
    (P.tensorProd Q).sub I = Q.sub I * P.sub I :=
  SubSystem.twist_sub_eq_mul_of_line _ _ I

theorem powsBundle_sub (F : LineBundle k x) : ∀ (t : ℕ) (L : Fin t → LineBundle k x) (n : Fin t → ℕ)
    (I : Chart x), (powsBundle F t L n).sub I = F.sub I * ∏ j, (L j).sub I ^ n j
  | 0, _, _, I => by simp [powsBundle]
  | t + 1, L, n, I => by
    rw [powsBundle, tensorProd_sub, LineBundle.powBundle_toSubSystem, SubSystem.pow_sub, powsBundle_sub F t,
      Fin.prod_univ_castSucc]
    ring

theorem twistBundle_sub (c : ℤ) (I : Chart x) : (twistBundle k x c).sub I = (twistSys k x c).sub I := rfl

theorem idealSys_sub (pp : Ideal (Poly k N)) (I : Chart x) : (idealSys x pp).sub I = idealMod (x := x) pp I := rfl

theorem supFam_sub {F G : SubFamily k x Ω} (I : Chart x) : (F.sup G).sub I = F.sub I ⊔ G.sub I := rfl

theorem spanBundle_sub (s : Ω) (hs : s ≠ 0) (I : Chart x) :
    (spanBundle k x s hs).sub I = Submodule.span (chartRing k x I) {s} := rfl

theorem prod_update_pow {M : Type*} [CommMonoid M] {t : ℕ} (a : Fin t → M) (n : Fin t → ℕ) (j : Fin t) :
    ∏ i, a i ^ Function.update n j (n j + 1) i = (∏ i, a i ^ n i) * a j := by
  calc ∏ i, a i ^ Function.update n j (n j + 1) i = ∏ i, (a i ^ n i * if i = j then a j else 1) :=
        Finset.prod_congr rfl fun i _ => by
          by_cases h : i = j
          · subst h
            simp [pow_succ]
          · simp [h]
    _ = (∏ i, a i ^ n i) * a j := by rw [Finset.prod_mul_distrib, Finset.prod_ite_eq']; simp

theorem mul_le_mul_sub {I : Chart x} {P Q P' Q' : Submodule (chartRing k x I) Ω} (h₁ : P ≤ P') (h₂ : Q ≤ Q') :
    P * Q ≤ P' * Q' :=
  Submodule.mul_le.mpr fun _ hp _ hq => Submodule.mul_mem_mul (h₁ hp) (h₂ hq)

theorem idealMod_le_one (pp : Ideal (Poly k N)) (I : Chart x) : idealMod (x := x) pp I ≤ 1 := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨f, m, e, -, hm, hf, hme, rfl⟩
  exact Submodule.mem_one.mpr ⟨⟨_, f, m, e, hm, hf, hme, rfl⟩, rfl⟩

attribute [local instance] MvPolynomial.gradedAlgebra in

theorem zeroIdeal_homog (D : SubSystem k x Ω) (s : Ω) :
    ∀ f ∈ zeroIdeal D s, ∀ d : ℕ, homogeneousComponent d f ∈ zeroIdeal D s := by
  have hJ : (zeroIdeal D s).IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) k) :=
    Ideal.homogeneous_span _ _ fun f ⟨c, hf, _⟩ => ⟨c, (mem_homogeneousSubmodule c f).mpr hf⟩
  intro f hf d
  have h := hJ d hf
  have hc : (DirectSum.decompose (homogeneousSubmodule (Fin (N + 1)) k) f d : Poly k N) =
      homogeneousComponent d f := decomposition.decompose'_apply f d
  rwa [hc] at h

theorem idealMod_sup_le (pp pp' : Ideal (Poly k N)) (hh : ∀ f ∈ pp, ∀ d : ℕ, homogeneousComponent d f ∈ pp)
    (hh' : ∀ f ∈ pp', ∀ d : ℕ, homogeneousComponent d f ∈ pp') (I : Chart x) :
    idealMod (x := x) (pp ⊔ pp') I ≤ idealMod (x := x) pp I ⊔ idealMod (x := x) pp' I := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨f, m, e, hf, hm, hfe, hme, rfl⟩
  obtain ⟨g, hg, z, hz, hgz⟩ := Submodule.mem_sup.mp hf
  have hfe' : f = homogeneousComponent e g + homogeneousComponent e z := by
    rw [← map_add, hgz, homogeneousComponent_eq_self hfe]
  rw [SetLike.mem_coe, hfe', map_add, add_div]
  exact Submodule.add_mem_sup
    (Submodule.subset_span ⟨_, m, e, hh g hg e, hm, homogeneousComponent_isHomogeneous _ _, hme, rfl⟩)
    (Submodule.subset_span ⟨_, m, e, hh' z hz e, hm, homogeneousComponent_isHomogeneous _ _, hme, rfl⟩)

theorem exists_dim_eq (pp : Ideal (Poly k N)) [pp.IsPrime] (hh : ∀ f ∈ pp, ∀ d : ℕ, homogeneousComponent d f ∈ pp)
    (hrel : ∃ i, (X i : Poly k N) ∉ pp) :
    ∃ e : ℕ, ringKrullDim (Poly k N ⧸ pp) = ((e + 1 : ℕ) : WithBot ℕ∞) := by
  have hge := one_le_ringKrullDim_of_relevant pp hh hrel
  have hle : ringKrullDim (Poly k N ⧸ pp) ≤ ((N + 1 : ℕ) : WithBot ℕ∞) := by
    refine (ringKrullDim_le_of_surjective _ Ideal.Quotient.mk_surjective).trans ?_
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    simp
  generalize ringKrullDim (Poly k N ⧸ pp) = d at hge hle
  induction d using WithBot.recBotCoe with
  | bot => exact absurd hge (by simp)
  | coe d =>
    induction d using ENat.recTopCoe with
    | top =>
      exfalso
      have h2 : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ (((N + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := hle
      exact ENat.natCast_ne_top (N + 1) (top_le_iff.mp (WithBot.coe_le_coe.mp h2))
    | coe m =>
      have h1 : 1 ≤ m := by exact_mod_cast hge
      exact ⟨m - 1, by rw [Nat.sub_add_cancel h1]; rfl⟩

end SnapperSections

open SnapperSections in

theorem SnapperSection.proof (hA : SnapperQuotAdd.Statement.{u, w, w})
    (hD : SnapperQuotDevissage.Statement.{u, w, w}) (hM : MulQuotEq.Statement.{u, w})
    (hN : SectionNonvanish.Statement.{u, w}) (hI : SectionMulInj.Statement.{u, w}) :
    SnapperSection.Statement.{u, w} := by
  intro k _ Ω _ _ N x pp hp hh hle hrel t L j a
  have := hp

  obtain ⟨μ, hμ⟩ := Generated.full k Ω N x (L j)
  obtain ⟨D, hDdef⟩ : ∃ D : LineBundle k x, D = (L j).tensorProd (twistBundle k x μ) := ⟨_, rfl⟩
  have hDgen : D.toSubSystem.Generated := hDdef ▸ hμ μ le_rfl
  have hDsub : ∀ I, D.sub I = (twistSys k x μ).sub I * (L j).sub I := fun I => by
    rw [hDdef, tensorProd_sub (L j) (twistBundle k x μ) I, twistBundle_sub]
  obtain ⟨s, hs, I₀, hsI₀⟩ := hN k Ω N x pp hp hh hle hrel D hDgen
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact hsI₀ (Submodule.zero_mem _)
  have hsD : ∀ I, s ∈ D.sub I := fun I => (Submodule.mem_iInf _).mp hs I
  obtain ⟨e, he⟩ := exists_dim_eq pp hh hrel
  obtain ⟨f₀, hf₀Z, hf₀p⟩ := CutZeroNotLe.proof k Ω N x e pp D s ⟨hp, hh, hle, hrel, he⟩ hs ⟨I₀, hsI₀⟩

  obtain ⟨Zs, hZs⟩ : ∃ Zs : Ideal (Poly k N), Zs = zeroIdeal D.toSubSystem s := ⟨_, rfl⟩
  have hZh : ∀ f ∈ Zs, ∀ d : ℕ, homogeneousComponent d f ∈ Zs := hZs ▸ zeroIdeal_homog _ s
  have hJh : ∀ f ∈ pp ⊔ Zs, ∀ d : ℕ, homogeneousComponent d f ∈ pp ⊔ Zs := by
    intro f hf d
    obtain ⟨g, hg, z, hz, rfl⟩ := Submodule.mem_sup.mp hf
    rw [map_add]
    exact Submodule.add_mem_sup (hh g hg d) (hZh z hz d)
  obtain ⟨F₁, hF₁def⟩ : ∃ F₁ : LineBundle k x, F₁ = (twistBundle k x a).tensorProd D := ⟨_, rfl⟩
  have hF₁sub : ∀ I, F₁.sub I = D.sub I * (twistSys k x a).sub I := fun I => by
    rw [hF₁def, tensorProd_sub (twistBundle k x a) D I, twistBundle_sub]
  obtain ⟨G₀, hG₀, -⟩ := IdealTwistFamily.proof k Ω N x F₁ pp hh
  have hG₀sub : ∀ I, G₀.sub I = idealMod (x := x) pp I * (D.sub I * (twistSys k x a).sub I) := fun I => by
    rw [hG₀, SubSystem.twist_sub_eq_mul_of_line, idealSys_sub]
    rw [hF₁sub]
  obtain ⟨F₂, hF₂def⟩ : ∃ F₂ : SubFamily k x Ω,
      F₂ = SubFamily.sup ((twistBundle k x a).tensorProd (spanBundle k x s hs0)).toSubFamily G₀ := ⟨_, rfl⟩
  have hF₂sub : ∀ I, F₂.sub I = Submodule.span (chartRing k x I) {s} * (twistSys k x a).sub I ⊔
      idealMod (x := x) pp I * (D.sub I * (twistSys k x a).sub I) := fun I => by
    rw [hF₂def, supFam_sub, tensorProd_sub (twistBundle k x a) (spanBundle k x s hs0) I, spanBundle_sub,
      twistBundle_sub, hG₀sub]
  have hF₂₁ : ∀ I, F₂.sub I ≤ F₁.sub I := fun I => by
    rw [hF₂sub, hF₁sub]
    refine sup_le (mul_le_mul_sub ((Submodule.span_singleton_le_iff_mem _ _).mpr (hsD I)) le_rfl) ?_
    exact (mul_le_mul_sub (idealMod_le_one pp I) le_rfl).trans_eq (one_mul _)
  have hJF : ∀ I, (F₁.toSubFamily.toSubSystem.twist (idealSys x (pp ⊔ Zs))).sub I ≤ F₂.sub I := fun I => by
    rw [SubSystem.twist_sub_eq_mul_of_line, idealSys_sub, hF₂sub]
    change idealMod (x := x) (pp ⊔ Zs) I * F₁.sub I ≤ _
    rw [hF₁sub]
    refine (mul_le_mul_sub (idealMod_sup_le pp Zs hh hZh I) le_rfl).trans ?_
    rw [Submodule.sup_mul]
    refine sup_le le_sup_right (le_sup_of_le_left ?_)
    rw [← mul_assoc, hZs]
    exact mul_le_mul_sub (StepThree.Away.idealMod_zeroIdeal_mul_le D.toSubSystem s I) le_rfl
  obtain ⟨r, qq, b, hqq, hdev⟩ := hD k Ω N x Ω F₁.toSubFamily F₂ F₁.fg hF₂₁ (pp ⊔ Zs) hJh
    (hle.trans le_sup_left) hJF
  refine ⟨μ, r, qq, b, fun m => ⟨(hqq m).1, (hqq m).2.1, lt_of_le_of_ne (le_sup_left.trans (hqq m).2.2)
    fun h => hf₀p ?_⟩, fun n c => ?_⟩
  · rw [h]
    exact (hqq m).2.2 (Ideal.mem_sup_right (hZs ▸ hf₀Z))

  obtain ⟨M, hMdef⟩ : ∃ M : LineBundle k x,
      M = (powsBundle (twistBundle k x a) t L n).tensorProd (twistBundle k x c) := ⟨_, rfl⟩
  have hMsub : ∀ I, M.sub I = (twistSys k x c).sub I * ((twistSys k x a).sub I * ∏ i, (L i).sub I ^ n i) :=
    fun I => by
      rw [hMdef, tensorProd_sub (powsBundle (twistBundle k x a) t L n) (twistBundle k x c) I, powsBundle_sub,
        twistBundle_sub, twistBundle_sub]
  have hMD : ∀ I, (M.tensorProd D).sub I = D.sub I * M.sub I := fun I => tensorProd_sub M D I
  obtain ⟨G₁, hG₁, -⟩ := IdealTwistFamily.proof k Ω N x (M.tensorProd D) pp hh
  have hG₁sub : ∀ I, G₁.sub I = idealMod (x := x) pp I * (D.sub I * M.sub I) := fun I => by
    rw [hG₁, SubSystem.twist_sub_eq_mul_of_line, idealSys_sub, hMD]
  obtain ⟨F₂', hF₂'def⟩ : ∃ F₂' : SubFamily k x Ω,
      F₂' = SubFamily.sup (M.tensorProd (spanBundle k x s hs0)).toSubFamily G₁ := ⟨_, rfl⟩
  have hF₂'sub : ∀ I, F₂'.sub I = Submodule.span (chartRing k x I) {s} * M.sub I ⊔
      idealMod (x := x) pp I * (D.sub I * M.sub I) := fun I => by
    rw [hF₂'def, supFam_sub, tensorProd_sub M (spanBundle k x s hs0) I, spanBundle_sub, hG₁sub]

  have hadd := hA k Ω N x Ω (M.tensorProd D).toSubFamily F₂' G₁ (M.tensorProd D).fg
    (fun I => by
      rw [hF₂'sub, hMD]
      refine sup_le (mul_le_mul_sub ((Submodule.span_singleton_le_iff_mem _ _).mpr (hsD I)) le_rfl) ?_
      exact (mul_le_mul_sub (idealMod_le_one pp I) le_rfl).trans_eq (one_mul _))
    (fun I => by rw [hF₂'sub, hG₁sub]; exact le_sup_right)

  have hmul := hM k Ω N x M.toSubSystem (M.toSubSystem.twist (idealSys x pp)) F₂'.toSubSystem G₁.toSubSystem s
    (fun I y hy => by
      rw [hF₂'sub]
      exact Submodule.mem_sup_left (Submodule.mul_mem_mul (Submodule.mem_span_singleton_self s) hy))
    (fun I z hz => by
      change z ∈ F₂'.sub I at hz
      rw [hF₂'sub] at hz
      obtain ⟨z₁, hz₁, z₂, hz₂, rfl⟩ := Submodule.mem_sup.mp hz
      obtain ⟨y, hy, rfl⟩ := Submodule.mem_span_singleton_mul.mp hz₁
      refine ⟨y, hy, ?_⟩
      rw [hG₁sub, add_sub_cancel_left]
      exact hz₂)
    (fun I y hy => by
      constructor
      · intro h
        refine hI k Ω N x pp hp hh hle D M s ⟨f₀, hf₀Z, hf₀p⟩ I y hy ?_
        rw [hG₁] at h
        exact h
      · intro h
        rw [SubSystem.twist_sub_eq_mul_of_line, idealSys_sub] at h
        rw [hG₁sub, show idealMod (x := x) pp I * (D.sub I * M.sub I) =
          idealMod (x := x) pp I * M.sub I * D.sub I by ring, mul_comm s y]
        exact Submodule.mul_mem_mul h (hsD I))

  have hE1 : pieceChar k pp a L (Function.update n j (n j + 1)) (c + μ) =
      eulerCharQuot k (M.tensorProd D).toSubSystem G₁.toSubSystem := by
    unfold pieceChar
    congr 1 <;> refine SubSystem.ext_sub fun I => ?_
    · rw [SubSystem.twist_sub_eq_mul_of_line, twistPows_sub, prod_update_pow, ← twistSys_sub_mul]
      rw [hMD, hMsub, hDsub]
      ring
    · rw [SubSystem.twist_sub_eq_mul_of_line, twistPows_sub, prod_update_pow, ← twistSys_sub_mul,
        SubSystem.twist_sub_eq_mul_of_line, idealSys_sub]
      rw [hG₁sub, hMsub, hDsub]
      ring
  have hE2 : pieceChar k pp a L n c = eulerCharQuot k M.toSubSystem (M.toSubSystem.twist (idealSys x pp)) := by
    unfold pieceChar
    congr 1 <;> refine SubSystem.ext_sub fun I => ?_
    · rw [SubSystem.twist_sub_eq_mul_of_line, twistPows_sub]
      rw [hMsub]
    · rw [SubSystem.twist_sub_eq_mul_of_line, twistPows_sub, SubSystem.twist_sub_eq_mul_of_line, idealSys_sub,
        SubSystem.twist_sub_eq_mul_of_line, idealSys_sub]
      rw [hMsub]
      ring
  have hE3 : eulerCharQuot k
      ((F₁.toSubFamily.toSubSystem.twistPows t (fun i => (L i).toSubSystem) n).twist (twistSys k x c))
      ((F₂.toSubSystem.twistPows t (fun i => (L i).toSubSystem) n).twist (twistSys k x c)) =
      eulerCharQuot k (M.tensorProd D).toSubSystem F₂'.toSubSystem := by
    congr 1 <;> refine SubSystem.ext_sub fun I => ?_
    · rw [SubSystem.twist_sub_eq_mul_of_line, twistPows_sub]
      rw [hF₁sub, hMD, hMsub]
      ring
    · rw [SubSystem.twist_sub_eq_mul_of_line, twistPows_sub]
      rw [hF₂sub, hF₂'sub, hMsub]
      simp only [← Submodule.add_eq_sup]
      ring
  rw [hE1, hE2, hadd, hmul, ← hE3, hdev t L n c]
  ring

end

end GroundTheory.Heights₂.Heights.Kleiman
