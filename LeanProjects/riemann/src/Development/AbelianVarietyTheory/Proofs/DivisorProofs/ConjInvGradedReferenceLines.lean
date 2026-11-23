import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HessRelFnB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCalcNumOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffAtLogNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedPointBelowAlgebraic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjPointNormPowEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FromModelOfLocMax
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNormalModelOverProjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinsumSubConst
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ScaleZeroComp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModelPresentingDivisor
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FamilyMetricsSmoothStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MetricConjugationSymmetryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeModelInducesRootMetricStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexPointsConnectedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagComponentProjectionSmoothStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorNormPullbackComponentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoverFunctionFieldEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleFiniteIndexStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermitianLineBundleInducedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HessianRelationInducedMetricStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HessianRelationLinearCombinationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChIntPullbackEqMongeAmpereStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundedSectionLogNormStatement

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Mean4O.ReadsEx

open InhabCalc CalcModel

section Generic

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

theorem exists_cover {C : CxSt F} {ι : Type} [Finite ι] (i₀ : ι) (A : ι → Adl C Y)
    (h₁ : ∀ i, LineNorm.FromModel Y (A i).D (eqn (A i).D) (A i).lg) (h₂ : ∀ i σ, C.mSmooth Y σ _ ((A i).m σ))
    (h₃ : ∀ i, ConjInv (A i)) : ∃ V : Cover Y, ∀ i, ∃ L, V.Induces (A i) L 1 := by
  classical
  have := Fintype.ofFinite ι
  choose M L m h using h₁
  obtain ⟨P, -, -, -, hP⟩ := LineNorm.Glue.exists_normal_dominating_finset (M i₀) M Finset.univ
  choose ρ hρ using fun i => hP i (Finset.mem_univ i)
  choose S hS using fun i => GlobalTheory.T.exists_line_bundle_finite_index F C Y (A i) P _ (m i) (m i).2
    (LineNorm.Add.GivenBy.pull (m := m i) (h i) (ρ i) (hρ i))
  let q : Polynomial Y.Fn := ∏ i, ∏ a ∈ S i, (Polynomial.X ^ (m i : ℕ) - Polynomial.C a)
  have hq : q ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.2 fun a _ =>
    Polynomial.X_pow_sub_C_ne_zero (m i).2 a
  obtain ⟨V, τ, ψ, e₁, e₂⟩ := GlobalTheory.T.exists_cover_function_field_embedding F Y P q.SplittingField
  refine ⟨V, fun i => ?_⟩
  obtain ⟨B, hB, r, hr⟩ := hS i V τ e₁ fun a ha => by
    have hd : Polynomial.X ^ (m i : ℕ) - Polynomial.C a ∣ q :=
      (Finset.dvd_prod_of_mem (fun a => Polynomial.X ^ (m i : ℕ) - Polynomial.C a) ha).trans
        (Finset.dvd_prod_of_mem (fun i => ∏ a ∈ S i, (Polynomial.X ^ (m i : ℕ) - Polynomial.C a)) (Finset.mem_univ i))
    have hs := (Polynomial.SplittingField.splits q).of_dvd (Polynomial.map_ne_zero hq)
      (Polynomial.map_dvd (algebraMap Y.Fn q.SplittingField) hd)
    obtain ⟨g, hg⟩ := hs.exists_eval_eq_zero (by
      rw [Polynomial.degree_map, Polynomial.degree_X_pow_sub_C (m i).pos]
      exact Nat.cast_ne_zero.2 (m i).ne_zero)
    refine ⟨ψ g, ?_⟩
    rw [← map_pow, ← e₂, RingHom.comp_apply]
    refine congrArg ψ (sub_eq_zero.1 ?_)
    simpa using hg
  exact GlobalTheory.T.exists_hermitian_line_bundle_induced F C Y V _ B r hB hr (h₂ i) (h₃ i)

theorem exists_pot {σ : F →+* ℂ} {Δ : Y.Dv} {m : (cxSt F).Met Y σ Δ} (h : (cxSt F).mSmooth Y σ Δ m) :
    ∃ Q : LocPot (Pts Y σ), IsPot id m Q ∧ M.IsPotential (atlasOf Y σ) Q := by
  have hp := presents_toLB Δ
  refine ⟨(Var.Met.toWeight m (Var.mSmooth.posSet_eq h) hp).locPot, fun x => ?_,
    (Var.mSmooth.isSmooth_toWeight h hp).isPotential (isAlgAtlas_atlasOf σ)⟩
  obtain ⟨f, hf⟩ := isPot_ofWeight (C := cxSt F) hp (Var.Met.toWeight m (Var.mSmooth.posSet_eq h) hp) x
  have e : (cxSt F).pn Y σ Δ ((cxSt F).ofWeight Y σ Δ _ _ hp (Var.Met.toWeight m (Var.mSmooth.posSet_eq h) hp)) =
      (cxSt F).pn Y σ Δ m := Var.pn_ofWeight_toWeight _ hp
  exact ⟨f, by simpa only [PosAt, lnN, e] using hf⟩

theorem exists_man {e : ℕ} (he : Y.dim = e) (Z : ∀ σ, Set (Pts Y σ)) (r : ∀ σ, Pts Y σ → ℝ)
    (h : ∀ σ, IsBd (atlasOf Y σ) (Z σ) (r σ) (fsPot Y σ)) :
    ∃ (M : Man e) (I : ManIs M Y), (∀ a z, z ∈ M.Z a ↔ I.pt a z ∈ Z _) ∧ (∀ a z, M.r a z = r _ (I.pt a z)) ∧
      ∀ (Δ : Y.Dv) (m : ∀ σ, (cxSt F).Met Y σ Δ), (∀ σ, (cxSt F).mSmooth Y σ Δ (m σ)) →
        ∃ Q : M.Pot, ∀ a, IsPot (I.pt a) (m _) (Q a) ∧ ReciprocityTheory.AnForm.M.IsPotential (M.A a) (Q a) := by
  subst he
  refine ⟨_, manIsOf Z r _ h, fun _ _ => Iff.rfl, fun _ _ => rfl, fun Δ m hm => ?_⟩
  choose Q hQ using fun σ => exists_pot (hm σ)
  exact ⟨fun a => Q _, fun a => hQ _⟩

theorem exists_lists {e : ℕ} {M : Man e} (I : ManIs M Y) {x : Y.X} (hx : IsClosed ({x} : Set Y.X)) :
    ∃ (d : ℕ) (z : ∀ a, Fin (d + 1) → M.X a), I.Lists x z := by
  obtain ⟨N, hN, hc⟩ := HtTwist.exists_card Y.str x hx
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN
  have h (a) : Nonempty (Fin (d + 1) ≃ {w : Pts Y (I.ε a) // under w = x}) :=
    ⟨(finCongr (hc ℂ (I.ε a)).symm).trans (Nat.equivFinOfCardPos ((hc ℂ (I.ε a)).trans_ne d.succ_ne_zero)).symm⟩
  refine ⟨d, fun a i => (I.pt a).symm ((h a).some i).1, fun a => ⟨(I.pt a).symm.injective.comp
    (Subtype.val_injective.comp (h a).some.injective), Set.ext fun w => ⟨?_, fun hw => ?_⟩⟩⟩
  · rintro ⟨i, rfl⟩
    simpa using ((h a).some i).2
  · exact ⟨(h a).some.symm ⟨I.pt a w, hw⟩, by simp⟩

theorem hessRel_dual {e : ℕ} {M : Man e} {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k}
    {ε : (k →+* ℂ) → Fin (M.n + 1)} {π : ∀ σ, CxPts p σ → M.X (ε σ)} {L : HermLB p} {P : M.Pot} (h : HessRel ε π L P) :
    HessRel ε π L.dual fun a => (P a).rsmul (-1) := fun σ c y hy i hi => by
  have key (g : ReciprocityTheory.L2DbarEstimates.V e → ℂ) (v) : ReciprocityTheory.L2DbarEstimates.cHess e (fun w => -g w) v = -ReciprocityTheory.L2DbarEstimates.cHess e g v := by
    have e₁ (b) : ReciprocityTheory.L2DbarEstimates.wdb e b (fun w => -g w) = fun w => -ReciprocityTheory.L2DbarEstimates.wdb e b g w := by
      funext w
      simp only [ReciprocityTheory.L2DbarEstimates.wdb, fderiv_fun_neg, neg_apply]
      ring
    ext a b
    simp only [ReciprocityTheory.L2DbarEstimates.cHess, Matrix.neg_apply, Matrix.of_apply, e₁, ReciprocityTheory.L2DbarEstimates.wd, fderiv_fun_neg,
      neg_apply]
    ring
  refine Eq.trans (congrArg (ReciprocityTheory.L2DbarEstimates.cHess e · _) (funext fun v => Complex.ofReal_neg _)) ((key _ _).trans
    ((congrArg (-·) (h σ c y hy i hi)).trans ((key _ _).symm.trans (congrArg (ReciprocityTheory.L2DbarEstimates.cHess e · _) ?_))))
  funext v
  simp [LocPot.rsmul]

theorem cls_eq {e : ℕ} {M : Man e} {ι : Type} [Fintype ι] [DecidableEq ι] (P : ι → M.Pot) (hP) (i : ι) :
    cls M P hP i = ((Pi.single i 1, 0) : (ι → ℝ) × smSub M) := by
  obtain rfl : ‹DecidableEq ι› = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  rfl

theorem exists_calc (hA : GlobalTheory.Published.ArCalc) (V : Cover Y) {e : ℕ} {M : Man e} (I : ManIs M Y) (he : Y.dim = e) {ι : Type}
    [Fintype ι] (L : ι → HermLB V.p) (P : ι → M.Pot) (hP : ∀ i a, ReciprocityTheory.AnForm.M.IsPotential (M.A a) (P i a))
    (h : ∀ ε π, V.IsDown I ε π → ∀ i, HessRel ε π (L i) (P i)) :
    ∃ Φ, ∀ ε π, V.IsDown I ε π → (calcWith P hP Φ).NumOn ε π V.ν L (cls M P hP) := by
  have hX : IsArithVar V.p e := he ▸ V.ar
  obtain ⟨Φ₀, hΦ₀⟩ := ((hA.arExists _ V.X V.p e hX).2 ι L).1
  refine ⟨V.ν⁻¹ • Φ₀, fun ε π hd => numOn_of hA.arChange hX _ _ (fun u hu hu' hc n f hf => ?_) fun n => ?_⟩
  · let K := calcWith P hP (V.ν⁻¹ • Φ₀)
    refine GlobalTheory.T.chInt_pullback_eq_monge_ampere F Y V e M I ε π he hd _ _ (K.firstChern_isPotential _) (GlobalTheory.T.hessian_relation_linear_combination F Y V e M I ε π hd _ _
      (fun o : Option ι => o.elim (fun a => LocPot.ofFun (u a)) P) n _ ?_ (K.firstChern_isPotential _) ?_ fun a j y hy w => ?_) f hf
    · rintro (_ | i) a
      · exact isPotential_ofFun _ _ (hu a)
      · exact hP i a
    · rintro (_ | i)
      · exact hessRel_fnB ε π u hu' hc
      · exact h ε π hd i
    · change leviL K a j y hy w _ = _
      rw [Fintype.sum_option, map_add, map_sum, map_smul, add_comm]
      refine congrArg₂ (· + ·) (congrArg (_ * ·) (K.c1_ar u hu a j y hy w)) (Finset.sum_congr rfl fun i _ => ?_)
      refine ((leviL K a j y hy w).map_smul _ _).trans ?_
      exact congrArg (_ * ·) (leviEq_of_φ _ (first_chern_class_potential M P hP i a) j y hy w)
  · have := calcWith_top P hP (V.ν⁻¹ • Φ₀) fun i => (n i : ℝ)
    erw [this]
    rw [LinearMap.smul_apply, smul_eq_mul, mul_inv_cancel_left₀ V.ν_pos.ne']
    exact hΦ₀.1 n

theorem conjInv_of_induced {C : CxSt F} {A : Adl C Y} {M : TrueGeo.Model Y} {L : HermLB M.p} {q : ℕ+}
    (h : A.Induced M L q 0) : LineNorm.FromModel Y A.D (eqn A.D) A.lg ∧ ConjInv A := by
  refine ⟨?_, fun σ σ' y y' e => ?_⟩
  · obtain ⟨-, r, hr, -, h₂⟩ := h
    exact ⟨M, L.B, q, r, L.isLB, hr, fun v e y yt i a b => by simpa using h₂ v e y yt i a b⟩
  · obtain ⟨N, π, -, hN, hπ, -, hj, -⟩ := ModelDom.exists_normal_dominating F Y M M
    exact (pow_left_inj₀ (C.pn_nonneg _ _ _ _ _ _) (C.pn_nonneg _ _ _ _ _ _) q.ne_zero).1
      (Cover.pn_pow_conj F C Y _ A _ _
        (Cover.induces_ofModel hN (InducedPull.induced_pull F C Y A M N π hπ hj L q 0 h)) σ σ' y y' e)

end Generic

section Flag

variable {D : D7} {O : Setup D}

theorem finite_steps (O : Setup D) : Finite {st // (letterOf O.S.Dw st).isSome} := by
  refine ((Set.finite_range fun x : Letter O.S.Dw => (Sum.inl (x.1, x.2) : ((D.host.E →+* ℂ) × ℕ) ⊕ ℕ)).union
    (Set.finite_range fun k : Fin (letters O.S.Dw).length => Sum.inr (k : ℕ))).subset ?_
  rintro (⟨τ, k⟩ | k) h
  · refine .inl ⟨⟨τ, ⟨k, by_contra fun hk => ?_⟩⟩, rfl⟩
    replace h : (letterOf O.S.Dw (.inl (τ, k))).isSome := h
    simp [letterOf, hk] at h
  · replace h : (letterOf O.S.Dw (.inr k)).isSome := h
    exact .inr ⟨⟨k, by simpa [letterOf] using h⟩, rfl⟩

theorem smooth_core (h : O.Core) (c : O.s.Comp) (σ : D.what₂.LL →+* ℂ) :
    (∀ n, (cxSt _).mSmooth _ σ _ (O.met.h0 c σ n)) ∧ (cxSt _).mSmooth _ σ _ ((O.met.ab c).m σ) := by
  obtain ⟨x, P, h⟩ := h
  rw [h.h0_eq, h.ab_eq]
  exact ⟨fun n => (GlobalTheory.T.family_metrics_smooth D _ _ _ _ _ O.s x O.Φ c σ n).2.1, P.ab_smooth c σ⟩

theorem conjInv_graded_reference_lines (h : O.Core) (c : O.s.Comp) (w : Sym D.host.E →₀ ℤ) : ConjInv (O.adl0 c w) := by
  obtain ⟨x, P, h⟩ := h
  intro σ σ' y y' e
  have hu : under y' = under y := by
    show below y'.1 = below y.1
    rw [e]
    exact HtIndep.below_spMap_comp _ _
  have h₁ : y ∈ Var.eqnSet σ (O.adl0 c w).D (eqn (O.adl0 c w).D (under y)) := Base.isEqn_eqn _ _
  have h₂ : y' ∈ Var.eqnSet σ' (O.adl0 c w).D (eqn (O.adl0 c w).D (under y')) := Base.isEqn_eqn _ _
  refine (Var.pn_frame h₂).trans (Eq.trans ?_ (Var.pn_frame h₁).symm)
  change Var.Met.h (O.met.h0 c σ' _) _ _ = Var.Met.h (O.met.h0 c σ _) _ _
  rw [hu, h.h0_eq]
  exact (GlobalTheory.T.metric_conjugation_symmetry D _ _ _ _ _ O.s x O.Φ c σ σ' _ y y' _ e h₁).2.1

theorem nonempty_latModel (h : O.Core) (P : Finset ℕ) (c : O.s.Comp) : Nonempty (O.LatModel P c) := by
  classical
  have := finite_steps O
  have : Finite {Q // Q ⊆ P} := (P.powerset.finite_toSet.subset fun _ hQ => Finset.mem_powerset.2 hQ).to_subtype
  have hab : LineNorm.FromModel _ (O.met.ab c).D (eqn (O.met.ab c).D) (O.met.ab c).lg ∧ ConjInv (O.met.ab c) := by
    obtain ⟨x, R, h⟩ := h
    obtain ⟨M, L, q, hq, -⟩ := R.ab_model c
    rw [h.ab_eq]
    exact conjInv_of_induced hq
  obtain ⟨hX, hN, M₀, ρ, hM₀, hρ⟩ := ModelOver.exists_normal_model D.what₂.LL (O.var c) (𝓞 O.κ.c.F)
    (RingOfIntegers.mapRingEquiv O.κ.e) O.s.T.Z.X O.s.T.Z.s ((O.Φ.C c).π ≫ genι O.s.T.Z) O.s.T.Z.proj (by
      rw [← (O.Φ.C c).π_str]
      simp only [Category.assoc]
      rw [pullback.condition_assoc, ← Spec.map_comp, ← Spec.map_comp]
      rfl)
  obtain ⟨V, hV⟩ := exists_cover (ι := Option ({Q // Q ⊆ P} × {st // (letterOf O.S.Dw st).isSome})) none
    (fun o => o.elim (O.met.ab c) fun a => O.adl0 c (Finsupp.single (ArIn.ind a.1.1, none, a.2.1) 1))
    (by
      rintro (_ | a)
      · exact hab.1
      · refine LineNorm.fromModel_lgOf (O.Φ.C c) HTBound.htBound hX M₀ ρ hM₀ hρ _ fun b hb => ?_
        obtain rfl := Finset.mem_singleton.1 (Finsupp.support_single_subset hb)
        exact a.1.1.finite_toSet.subset fun q hq => of_decide_eq_true hq)
    (by
      rintro (_ | a) σ
      exacts [(smooth_core h c σ).2, (smooth_core h c σ).1 _])
    (by
      rintro (_ | a)
      exacts [hab.2, conjInv_graded_reference_lines h c _])
  choose L hL using hV
  refine ⟨⟨V, fun Q st => if e : Q ⊆ P ∧ (letterOf O.S.Dw st).isSome then L (some (⟨Q, e.1⟩, ⟨st, e.2⟩))
    else HermLB.triv _, fun Q hQ st hst => ?_, 1, one_pos, L none, hL none⟩⟩
  rw [dif_pos ⟨hQ, hst⟩]
  exact hL (some (⟨Q, hQ⟩, ⟨st, hst⟩))

theorem isBd_core (h : O.Core) (c : O.s.Comp) (σ : D.what₂.LL →+* ℂ) :
    IsBd (atlasOf (O.var c) σ) {z | (O.Φ.C c).π (under z) ∈ genBd O.s.T.Z} (O.met.r c σ) (fsPot _ σ) := by
  obtain ⟨x, P, h⟩ := h
  have := GlobalTheory.T.complex_points_connected _ (O.var c) σ
  have := CxPts.t2Space_cxPts_of_isProjOver σ (O.var c).isProjOver
  obtain ⟨L, t, h₁⟩ := GlobalTheory.T.exists_bounded_section_log_norm _ (O.var c) σ x.m (fun i => (x.cpt i).preimage (O.Φ.C c).π.continuous)
    (fun i z => x.nrm _ i ((O.Φ.C c).down z))
    (fun i => GlobalTheory.T.divisor_norm_pullback_component D _ _ _ _ _ O.s O.Φ c _ _ _ (GlobalTheory.T.flag_component_projection_smooth D _ _ _ _ _ O.s O.Φ c) (x.nrm_div _ i))
    (fun i hi => CartierDiv.genericPoint_notMem_supp (O.Φ.C c).bd (((O.Φ.C c).bd_supp _).2
      (x.cpt_list.2.1.le (Set.mem_iUnion.2 ⟨i, hi⟩))))
  rw [h.r_eq, show {z : Pts (O.var c) σ | (O.Φ.C c).π (under z) ∈ genBd O.s.T.Z} = _ from
    Set.ext fun z => x.liesIn_genBd_iff ((O.Φ.C c).down z)]
  exact isBd_of_isBdSec _ _ _ _ _ _ L t (isBd_fsPot σ).2.2.1 (isBd_fsPot σ).2.2.2.1 h₁

variable (O) in

def chgL (c : O.s.Comp) (R : Option ℝ) {e : ℕ} {M : Man e} (I : ManIs M (O.var c)) :
    (D.what₂.Tau → Fin O.N → ℝ) →ₗ[ℝ] M.Fun where
  toFun u a z := O.chg c R u _ (I.pt a z)
  map_add' u v := by
    funext a z
    simp [Setup.chg, add_mul, Finset.sum_add_distrib]
  map_smul' t u := by
    funext a z
    simp [Setup.chg, Finset.mul_sum, mul_assoc]

def wtL (T : Type) (N : ℕ) : (T → Fin N → ℝ) →ₗ[ℝ] (Option (T × Fin N) → ℝ) where
  toFun u o := o.elim 0 fun x => u x.1 x.2
  map_add' u v := by
    funext o
    cases o <;> simp
  map_smul' t u := by
    funext o
    cases o <;> simp

theorem wtL_single {T : Type} {N : ℕ} {_ : DecidableEq T} {_ : DecidableEq (Fin N)} {_ : DecidableEq (Option (T × Fin N))}
    (τ : T) (i : Fin N) : wtL T N (Pi.single τ (Pi.single i 1)) = Pi.single (some (τ, i)) 1 := by
  funext o
  rcases o with _ | ⟨τ', i'⟩
  · simp [wtL]
  · by_cases hτ : τ' = τ
    · subst hτ
      simp [wtL, Pi.single_apply]
    · simp [wtL, hτ]

theorem smul_single_inv {J : Type} {d d' : DecidableEq J} {t : ℝ} (h : t ≠ 0) (j : J) :
    t • (@Pi.single J (fun _ => ℝ) _ d j t⁻¹) = @Pi.single J (fun _ => ℝ) _ d' j 1 := by
  obtain rfl : d = d' := Subsingleton.elim _ _
  rw [← Pi.single_smul', smul_eq_mul, mul_inv_cancel₀ h]

def meanL {e : ℕ} (M : Man e) {d : ℕ} (z : ∀ a, Fin (d + 1) → M.X a) : M.Fun →ₗ[ℝ] ℝ where
  toFun g := M.κ * ∑ a, (∑ i, g a (z a i)) / ((d : ℝ) + 1)
  map_add' u v := by simp [add_div, mul_add, Finset.sum_add_distrib]
  map_smul' t u := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, ← Finset.mul_sum, mul_div_assoc]
    ring

theorem isClosed_basePt (y : Pt O.s) : IsClosed ({basePt O.Φ y} : Set (O.var (compPt O.s y)).X) := by
  obtain ⟨p, -, -, hp⟩ := liesUnder_basePt O.Φ y
  rw [← hp]
  exact isClosed_below_algebraic _ _ p

theorem exists_reads (hA : GlobalTheory.Published.ArCalc) (h : O.Core) : ∃ A T H, Nonempty (O.Reads A T H) := by
  classical
  choose M I hZ hr hQ using fun c => exists_man (e := WeightThresholdDefs.dimY O.Y) (O.dim_eq c) _ _ (isBd_core h c)
  choose Q hQ₁ using fun c (x : DV.Rt D.what₂.Tau O.N) => hQ c _ (fun σ => O.met.h0 c σ (O.ex x))
    fun σ => (smooth_core h c σ).1 _
  choose Qa hQ₂ using fun c => hQ c _ (O.met.ab c).m fun σ => (smooth_core h c σ).2
  let W (P : Finset ℕ) (c : O.s.Comp) : O.LatModel P c := (nonempty_latModel h P c).some
  let S (B : ℝ) : Finset ℕ := FlagAr.setB O.Y B
  let P (B : ℝ) (c : O.s.Comp) : Option (DV.Rt D.what₂.Tau O.N) → (M c).Pot := fun o a =>
    o.elim ((Qa c a).rsmul (W (S B) c).k) fun x => ((Q c x a).rsmul (1 : ℕ)).rsmul (-1)
  have hP (B c o a) : ReciprocityTheory.AnForm.M.IsPotential ((M c).A a) (P B c o a) := by
    cases o with
    | none => exact isPotentialRsmul _ _ _ (hQ₂ c a).2
    | some x => exact isPotentialRsmul _ _ _ (isPotentialRsmul _ _ _ (hQ₁ c x a).2)
  have hD : O.DualRef := fun c σ x z f hf => h.referenceMetric_mul_dual_eq_one c σ _ hf
  choose Φ hΦ using fun B c => exists_calc hA (W (S B) c).V (I c) (O.dim_eq c) ((W (S B) c).gens (S B)) (P B c) (hP B c)
    fun ε π hd o => by
      cases o with
      | none => exact GlobalTheory.T.hessian_relation_induced_metric _ _ _ _ _ _ _ ε π hd _ _ _ _ (W (S B) c).amp_spec (hQ₂ c)
      | some x =>
        refine hessRel_dual (GlobalTheory.T.hessian_relation_induced_metric _ _ _ _ _ _ _ ε π hd _ _ _ _
          (GlobalTheory.T.lattice_model_induces_root_metric D O hD _ c (W (S B) c) _ subset_rfl x) ?_)
        have key (r) (hr : r = O.ex x) (a) : IsPot ((I c).pt a) (O.met.h0 c _ r) (Q c x a) := hr ▸ (hQ₁ c x a).1
        exact fun a => ⟨key _ (expo_rootSym _ _ _ _ _) a, (hQ₁ c x a).2⟩
  have hm (B c) : (((W (S B) c).mult : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (W (S B) c).mult_pos.ne'
  let F (c : O.s.Comp) : An (M c) D.what₂.Tau O.N :=
    { th := fun u a => combPot (fun x => Q c x a) (fun x => -u x.1 x.2) 0
      a := fun a => (Qa c a).rsmul (((O.met.ab c).n : ℕ) : ℝ)⁻¹
      ph := chgL O c none (I c)
      phR := fun R => chgL O c (some R) (I c)
      phS := fun u s a z => O.met.reg c _ u (Real.exp (-(s ^ 2)⁻¹)) ((I c).pt a z) / 2 }
  let T : Real0 O.Y :=
    { M := M, F := F
      K := fun B c => calcWith (P B c) (hP B c) (Φ B c)
      L := fun B c => (LinearMap.inl ℝ _ (smSub (M c))).comp (wtL _ _)
      a := fun B c => ((Pi.single none (((W (S B) c).mult : ℕ) : ℝ)⁻¹, 0) : _ × smSub (M c))
      th_pot := fun c u a => isPotential_combPot _ _ (fun x => (hQ₁ c x a).2) _ _ fun _ => contDiffOn_const
      a_pot := fun c a => isPotentialRsmul _ _ _ (hQ₂ c a).2
      c1_L := fun B c u a => leviEq_of_φ _ (by
        funext x y
        change ∑ o, wtL _ _ u o * (P B c o a).φ x y + 0 = ∑ z : DV.Rt D.what₂.Tau O.N, -u z.1 z.2 * (Q c z a).φ x y + 0
        rw [Fintype.sum_option]
        refine congrArg (· + 0) ((congrArg (· + _) (zero_mul _)).trans ((zero_add _).trans
          (Finset.sum_congr rfl fun z _ => ?_)))
        change u z.1 z.2 * (-1 * (((1 : ℕ) : ℝ) * (Q c z a).φ x y)) = _
        simp)
      firstChern_leviEq_constant := fun B c a => leviEq_of_φ _ (by
        funext x y
        change ∑ o, (Pi.single none (((W (S B) c).mult : ℕ) : ℝ)⁻¹ : Option (DV.Rt D.what₂.Tau O.N) → ℝ) o *
          (P B c o a).φ x y + 0 = (((O.met.ab c).n : ℕ) : ℝ)⁻¹ * (Qa c a).φ x y
        have : (((W (S B) c).k : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (W (S B) c).k_pos.ne'
        simp only [Fintype.sum_option, P, LocPot.rsmul, Option.elim, Setup.LatModel.mult, Pi.single_eq_same,
          Pi.single_eq_of_ne (Option.some_ne_none _), zero_mul, Finset.sum_const_zero, add_zero, Nat.cast_mul]
        field_simp) }
  choose d z hz using fun y : Pt O.s => exists_lists (I _) (isClosed_basePt y)
  let cj (c : O.s.Comp) (y : Pt O.s) : ∀ a, Fin (d y + 1) → (M c).X a :=
    if e : compPt O.s y = c then e ▸ z y else fun _ _ => Classical.arbitrary _
  have hcj (y : Pt O.s) : cj _ y = z y := dif_pos rfl
  let hg (B : ℝ) (c : O.s.Comp) (y : Pt O.s) : Option (DV.Rt D.what₂.Tau O.N) → ℝ := fun o =>
    o.elim ((W (S B) c).mult * (O.met.ab c).ht (baseOn O.Φ c y)) fun x => -(O.root0 c (S B) x).ht (baseOn O.Φ c y)
  let Pp : T.Pts :=
    { d := d, conj := cj
      ht := fun B c y => (Fintype.linearCombination ℝ (hg B c y)).coprod
        ((meanL (M c) (cj c y)).comp (smSub (M c)).subtype) }
  refine ⟨O.aux fun _ _ => 0, T, O.hts, ⟨⟨O.heightData_satisfies _, O.htIs_hts, I, fun c => ⟨hZ c, fun a z _ => hr c a z,
    fun u a => ⟨fun x => Q c x a, fun x => hQ₁ c x a, fun j y hy w => ?_⟩,
    fun a => ⟨fun _ => Qa c a, fun _ => hQ₂ c a, fun j y hy w => ?_⟩, fun _ _ _ _ => rfl, fun _ _ _ _ _ => rfl,
    fun _ _ _ _ _ => rfl⟩, Pp, ⟨fun y => ?_, fun B y g hg' => ?_, fun B _ y u => ?_, fun B _ y => ?_⟩, W,
    fun B _ c ε π hd => ?_⟩⟩⟩
  · let K := calcOf (M c) (Q c) fun x a => (hQ₁ c x a).2
    have e : (show K.V from (fun x : DV.Rt D.what₂.Tau O.N => -u x.1 x.2, 0)) = ∑ x, (-u x.1 x.2) • cls (M c) (Q c) (fun x a => (hQ₁ c x a).2) x := by
      simp only [cls_eq]
      change (_ : (_ → ℝ) × smSub (M c)) = ∑ x : DV.Rt D.what₂.Tau O.N, (-u x.1 x.2) • ((Pi.single x 1, 0) : (_ → ℝ) × smSub (M c))
      refine Prod.ext (funext fun x => ?_) ?_
      · simp [Prod.fst_sum, Pi.single_apply]
      · simp [Prod.snd_sum]
    change leviL K a j y hy w (show K.V from (fun x : DV.Rt D.what₂.Tau O.N => -u x.1 x.2, 0)) = _
    rw [e, map_sum]
    refine Finset.sum_congr rfl fun x _ => ((leviL K a j y hy w).map_smul _ _).trans ?_
    exact congrArg (_ * ·) (leviEq_of_φ _ (first_chern_class_potential _ _ _ x a) j y hy w)
  · rw [Fintype.sum_unique]
    have h₁ := levi_add_smul (f := fun _ => (0 : ℝ)) (((O.met.ab c).n : ℕ) : ℝ)⁻¹ contDiffAt_const
      (LeviOnly.pot_two (hQ₂ c a).2 _ j hy ((Qa c a).mem_U _)) w
    have h₂ : levi (fun _ : Fin (WeightThresholdDefs.dimY O.Y) → ℂ => (0 : ℝ)) y w = 0 := by simp [levi]
    simp only [zero_add, h₂] at h₁
    exact h₁
  · change (I _).Lists _ (cj _ y)
    rw [hcj]
    exact hz y
  · change Fintype.linearCombination ℝ _ 0 + meanL (M _) (cj _ y) (smProj (M (compPt O.s y)) g).1 = _
    rw [map_zero, zero_add, smProj_of_smooth _ hg']
    rfl
  · change Fintype.linearCombination ℝ (hg B _ y) (wtL _ _ u) + meanL (M _) (cj _ y) 0 = _
    rw [map_zero, add_zero, Fintype.linearCombination_apply, Fintype.sum_option]
    simp [wtL, hg, Setup.htWt, S]
  · change Fintype.linearCombination ℝ (hg B _ y) (Pi.single none _) + meanL (M _) (cj _ y) 0 = _
    rw [map_zero, add_zero, Fintype.linearCombination_apply_single, smul_eq_mul]
    exact inv_mul_cancel_left₀ (hm B _) _
  · have e : T.gen B c (W (S B) c).mult = cls (M c) (P B c) (hP B c) := by
      funext o
      refine Eq.trans ?_ (cls_eq _ _ o).symm
      rcases o with _ | ⟨τ, i⟩
      · exact Prod.ext (smul_single_inv (hm B c) none) (smul_zero _)
      · refine Prod.ext ?_ rfl
        simp only [Real0.gen, Option.elim]
        exact wtL_single τ i
    rw [e]
    exact hΦ B c ε π hd

end Flag

theorem main : GlobalTheory.Published.ArCalc → ∀ (D : D7) (O : Setup D), O.Core →
    ∃ A T H, Nonempty (O.Reads A T H) ∧ ObjCore O.Y A T H := fun hA _ O h =>
  have ⟨A, T, H, ⟨r⟩⟩ := exists_reads hA h
  ⟨A, T, H, ⟨r⟩, .mk O h r⟩

end GlobalTheory.Mean4O.ReadsEx
