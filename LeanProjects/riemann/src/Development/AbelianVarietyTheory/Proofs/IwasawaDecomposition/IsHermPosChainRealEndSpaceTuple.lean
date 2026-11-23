import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.IsMultMapUnivZero
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Formalism.LocalToGlobal.IndefiniteReal.BridgeSeed
import Formalism.LocalToGlobal.IndefiniteReal.LinksExistW
import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.OneLeAPlLast

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HilbertLevels

section Gen

open Formalism.IndefR.Lev
open scoped ComplexOrder

theorem aniso_of_sig {n : ℕ} (G : Matrix (Fin n) (Fin n) ℂ) {p q : ℕ} (h : Formalism.UG.HasSignature G p q)
    (hpq : p = 0 ∨ q = 0) (x : Fin n → ℂ) (hx : star x ⬝ᵥ (G *ᵥ x) = 0) : x = 0 := by
  obtain ⟨hn, Q, hQ⟩ := Formalism.UG.P.sig_data G p q h
  have hJ : Formalism.UG.Jpq p q * Formalism.UG.Jpq p q = 1 := by
    simp [Formalism.UG.Jpq, Matrix.fromBlocks_multiply]
  have e : Fin n ≃ Fin p ⊕ Fin q := Fintype.equivOfCardEq (by simpa using hn)
  have h1 : (Formalism.UG.Jpq p q * Qᴴ * G) * Q = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Qᴴ, hQ, hJ]
  have h2 := (Matrix.mul_eq_one_comm_of_equiv e.symm).1 h1
  obtain ⟨y, rfl⟩ : ∃ y, x = Q *ᵥ y := ⟨(Formalism.UG.Jpq p q * Qᴴ * G) *ᵥ x, by rw [Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]⟩
  rw [Formalism.UG.P.sig_quad G Q hQ] at hx
  have key : ∀ {m : ℕ} (z : Fin m → ℂ), ∑ i, star (z i) * z i = 0 → ∀ i, z i = 0 := fun z hz i =>
    congrFun (dotProduct_star_self_eq_zero.1 hz) i
  have : y = 0 := by
    funext k
    rcases hpq with rfl | rfl
    · rcases k with k | k
      · exact k.elim0
      · exact key (fun j => y (Sum.inr j)) (by simpa using hx) k
    · rcases k with k | k
      · exact key (fun j => y (Sum.inl j)) (by simpa using hx) k
      · exact k.elim0
  rw [this, Matrix.mulVec_zero]

variable {D : D7}

theorem aniso {V : HSp D} (hs : V.SigOK) (hd : V.IsDefinite) (τ : D.host.E →+* ℂ) (x : Fin V.rank → ℂ)
    (hx : star x ⬝ᵥ (V.gram.map τ *ᵥ x) = 0) : x = 0 :=
  aniso_of_sig _ (hs τ) (by rcases hd τ with h | h <;> simp [h]) x hx

theorem sign_eq {V : HSp D} (hs : V.SigOK) (hd : V.IsDefinite) {S : D.what₂.Tau → SPar} (M : DSModel V S)
    (τ : D.what₂.Tau) (a b : Fin V.rank) : M.ε τ a = M.ε τ b := by
  by_contra hab
  have hne : a ≠ b := fun h => hab (by rw [h])
  have hu := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  set y : Fin V.rank → ℂ := Pi.single a 1 + Pi.single b 1 with hy
  have hx : M.fr τ *ᵥ ((M.fr τ)⁻¹ *ᵥ y) = y := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
  have h0 := aniso hs hd (tauE D τ) ((M.fr τ)⁻¹ *ᵥ y) (by
    have e : V.gram.map (tauE D τ) = (M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ := (M.fr_gram τ).symm
    rw [e, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hx, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, hx, hy]
    simp only [star_add, add_dotProduct, ← Pi.single_star, star_one, single_dotProduct, Formalism.REAL.Jm,
      Matrix.mulVec_diagonal, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hne, Pi.single_eq_of_ne hne.symm]
    cases h1 : M.ε τ a <;> cases h2 : M.ε τ b <;> simp_all)
  rw [h0, Matrix.mulVec_zero] at hx
  have := congrFun hx a
  simp [hy, Pi.single_eq_of_ne hne] at this

theorem finiteDimensional_model {V : HSp D} (hs : V.SigOK) (hd : V.IsDefinite) {S : D.what₂.Tau → SPar}
    (M : DSModel V S) (τ : D.what₂.Tau) : FiniteDimensional ℂ (M.H τ) := by
  obtain ⟨-, -, -, hirr, -, ⟨U, hfd, hst, -, ⟨v, hv, hv0, -⟩, -⟩, -⟩ := M.ds τ
  have hJ : ∃ c : ℂ, c ≠ 0 ∧ Formalism.REAL.Jm (M.ε τ) = c • (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) := by
    rcases isEmpty_or_nonempty (Fin V.rank) with h | ⟨⟨a⟩⟩
    · exact ⟨1, one_ne_zero, Subsingleton.elim _ _⟩
    · refine ⟨if M.ε τ a then 1 else -1, by split_ifs <;> simp, ?_⟩
      rw [Matrix.smul_one_eq_diagonal, Formalism.REAL.Jm]
      congr 1
      funext b
      rw [sign_eq hs hd M τ a b]
  obtain ⟨c, hc, hJ⟩ := hJ
  have hU := hirr U U.closed_of_finiteDimensional fun g hg => hst g (by
    have hg' : gᴴ * Formalism.REAL.Jm (M.ε τ) * g = Formalism.REAL.Jm (M.ε τ) := hg
    refine ⟨Matrix.mem_unitaryGroup_iff'.2 ?_, by rw [hJ]; simp⟩
    rw [hJ, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul] at hg'
    exact smul_right_injective _ hc hg')
  rcases hU with rfl | rfl
  · exact absurd ((Submodule.mem_bot ℂ).1 hv) hv0
  · exact Submodule.topEquiv.finiteDimensional

theorem finrank_model_pos {V : HSp D} (hs : V.SigOK) (hd : V.IsDefinite) {S : D.what₂.Tau → SPar}
    (M : DSModel V S) (τ : D.what₂.Tau) : 0 < Module.finrank ℂ (M.H τ) := by
  haveI := finiteDimensional_model hs hd M τ
  haveI : Nontrivial (M.H τ) := (M.ds τ).2.1
  exact Module.finrank_pos

theorem multT_mono {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S) {J J' : Set (GA D V)}
    {χ χ' : GA D V → ℂ} (h : ∀ k ∈ J', k ∈ J ∧ χ k = χ' k) : MultT θ M J χ ≤ MultT θ M J' χ' :=
  Submodule.map_mono (Submodule.span_mono fun X hX =>
    ⟨hX.aut, hX.cusp, fun v k hk g => (h k hk).2 ▸ hX.lev v k (h k hk).1 g, hX.equiv, hX.cont⟩)

theorem levS_mono {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L L' : LevDat D.host.E ℂ V.rank}
    (h : ∀ x ∈ lev D.sp.cm V.gram β L', x ∈ lev D.sp.cm V.gram β L ∧ levFn β L' x = levFn β L x) :
    ∀ k ∈ levS V β L', k ∈ levS V β L ∧ levChi V β L k = levChi V β L' k := by
  intro k hk
  obtain ⟨h1, h2⟩ := h _ hk.2
  exact ⟨⟨hk.1, h1⟩, (congrArg (fun u : ℂˣ => (u : ℂ)) h2).symm⟩

variable {n : ℕ} {J : Matrix (Fin n) (Fin n) D.host.E} {β : GL (Fin n) (Lev.EAf D)}

theorem lev_datY_triv (r t j : ℕ) (hr : r ≤ n) (Pg Q : Finset (Pl D.host.E)) (P : LevelP Pg r ℂ)
    (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (x)
    (hx : x ∈ lev D.sp.cm J β (datY n r t j hr Pg Q (LevelP.triv Pg r ℂ) χ ξ Frm.B)) :
    x ∈ lev D.sp.cm J β (datY n r t j hr Pg Q P χ ξ Frm.B) ∧
      levFn β (datY n r t j hr Pg Q (LevelP.triv Pg r ℂ) χ ξ Frm.B) x = levFn β (datY n r t j hr Pg Q P χ ξ Frm.B) x := by
  have h1 : rTup β (datY n r t j hr Pg Q (LevelP.triv Pg r ℂ) χ ξ Frm.B) x = 1 := by
    exact Subgroup.mem_bot.1 (show _ ∈ (⊥ : Subgroup (G0 Pg r)) from hx.2)
  have h1' : rTup β (datY n r t j hr Pg Q P χ ξ Frm.B) x = 1 := h1
  refine ⟨⟨hx.1, ?_⟩, ?_⟩
  · rw [h1']; exact Subgroup.one_mem _
  · unfold levFn
    rw [h1, h1', blockDiagonalExtendByOnePrimeField_one, blockDiagonalExtendByOnePrimeField_one]
    rfl

theorem lev_datY_zero {r : ℕ} (hn : n ≤ r) (t : ℕ) (hr : r ≤ n) (Pg Q : Finset (Pl D.host.E)) (P : LevelP Pg r ℂ)
    (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (x)
    (hx : x ∈ lev D.sp.cm J β (datY n r t 0 hr Pg Q (LevelP.triv Pg r ℂ) χ ξ Frm.B)) :
    x ∈ lev D.sp.cm J β (datY n r t 0 hr Pg ∅ P χ (fun _ => 1) Frm.B) ∧
      levFn β (datY n r t 0 hr Pg Q (LevelP.triv Pg r ℂ) χ ξ Frm.B) x =
        levFn β (datY n r t 0 hr Pg ∅ P χ (fun _ => 1) Frm.B) x := by
  have h1 : rTup β (datY n r t 0 hr Pg Q (LevelP.triv Pg r ℂ) χ ξ Frm.B) x = 1 := by
    exact Subgroup.mem_bot.1 (show _ ∈ (⊥ : Subgroup (G0 Pg r)) from hx.2)
  have h1' : rTup β (datY n r t 0 hr Pg ∅ P χ (fun _ => 1) Frm.B) x = 1 := h1
  have hp := mem_parLev.1 hx.1
  refine ⟨⟨mem_parLev.2 ⟨hp.1, hp.2.1, hp.2.2.1, fun PP hP => absurd hP (Finset.notMem_empty PP)⟩, ?_⟩, ?_⟩
  · rw [h1']; exact Subgroup.one_mem _
  · have hd : ∀ PP ∈ Q, dBlk (blk2 r) 1 (redFn β PP x) = 1 := by
      intro PP hP
      have hm : redFn β PP x ∈ blockTri (blk2 r) := hp.2.2.2 PP hP
      refine Units.ext ?_
      rw [diag_block_det_val 1 hm]
      haveI : IsEmpty {a : Fin n // blk2 r a = 1} := ⟨fun a => by
        have ha := a.2
        have : a.1.val < r := lt_of_lt_of_le a.1.2 hn
        simp [blk2, this] at ha⟩
      simp
    unfold levFn
    rw [h1, h1', blockDiagonalExtendByOnePrimeField_one, blockDiagonalExtendByOnePrimeField_one]
    simp only [datY, if_true, Finset.range_zero, Finset.prod_empty, Finset.prod_const_one, mul_one, one_mul]
    exact Finset.prod_eq_one fun PP hP => by rw [hd PP hP, map_one]

end Gen

section Main

open Formalism.IndefR.Lev Formalism.IndefR.RecTie Formalism.IndefR.PeterssonHilbertSpace

theorem ipVia_apply {H N : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [AddCommGroup N] [Module ℂ N]
    (e : H →ₗ[ℂ] N) (he : Function.Injective e) (a b : H) : ipVia e (e a) (e b) = ⟪a, b⟫_ℂ := by
  classical
  have h : e a ∈ LinearMap.range e ∧ e b ∈ LinearMap.range e := ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩
  unfold ipVia
  rw [dif_pos h, he h.1.choose_spec, he h.2.choose_spec]

theorem isHermPos_ipVia {H N : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    [AddCommGroup N] [Module ℂ N] (e : H →ₗ[ℂ] N) (he : Function.Injective e) :
    IsHermPos (LinearMap.range e) (ipVia e) where
  fd := inferInstance
  add := by
    rintro ⟨_, a, rfl⟩ ⟨_, a', rfl⟩ ⟨_, c, rfl⟩
    simp only
    rw [← map_add, ipVia_apply e he, ipVia_apply e he, ipVia_apply e he, inner_add_left]
  smul := by
    rintro s ⟨_, a, rfl⟩ ⟨_, c, rfl⟩
    simp only
    rw [← map_smul, ipVia_apply e he, ipVia_apply e he, inner_smul_left]
  herm := by
    rintro ⟨_, a, rfl⟩ ⟨_, c, rfl⟩
    simp only
    rw [ipVia_apply e he, ipVia_apply e he, inner_conj_symm]
  pos := by
    rintro ⟨_, a, rfl⟩ hx
    simp only
    have ha : a ≠ 0 := fun h => hx (Subtype.ext (by simp [h]))
    have h1 : 0 < ‖a‖ := norm_pos_iff.2 ha
    have h2 : (⟪a, a⟫_ℂ).re = ‖a‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) a
    rw [ipVia_apply e he, h2]
    positivity

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem herm_lev (hI : Inputs D) {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} (hs : V.SigOK) {S : D.what₂.Tau → SPar}
    (M : DSModel V S) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) {μ : Measure (GA D V)}
    {𝓕 : Set (GA D V)} (hH : μ.IsHaarMeasure) (hF : IsFundamentalDomain (GQ V) 𝓕 μ) :
    IsHermPos (MultT θ M (levS V β L) (levChi V β L)) (ipMT M μ 𝓕) :=
  isHermPos_multT M μ 𝓕 θ _ _ hθ (hI.hc V hs S θ M _ _) (hI.lev V β L).2 (hI.schur V hs S θ M _ _ μ 𝓕) hH hF
    (hI.pet V μ 𝓕 hH hF) (hI.sm V S M)

theorem nP_pos (F : Face D A) (b : Bool) : 0 < RealDat.nP F b := by
  unfold RealDat.nP
  exact_mod_cast Nat.card_pos

theorem scaled {V : HSp D} {μ : Measure (GA D V)} {𝓕 : Set (GA D V)} {c : ℝ} (hc : 0 < c) (hH : μ.IsHaarMeasure)
    (hF : IsFundamentalDomain (GQ V) 𝓕 μ) :
    (ENNReal.ofReal c • μ).IsHaarMeasure ∧ IsFundamentalDomain (GQ V) 𝓕 (ENNReal.ofReal c • μ) :=
  ⟨Measure.IsHaarMeasure.smul μ (by simpa using hc) ENNReal.ofReal_ne_top,
    hF.mono Measure.smul_absolutelyContinuous⟩

theorem rank_lowerChainSpace_zero_le : (Yc D 0).rank ≤ D.R.r := by
  have h1 := D.sp.Y_rank (min 0 D.R.m) (min_le_right _ _)
  have h2 : D.R.rankY (min 0 D.R.m) = D.R.r := by simp [Ranks.rankY]
  exact (h1.trans h2).le

variable (R : RealDat D A Ks) (F : Face D A) (tupT : D.what₂.Tup → T) (hm : 0 < D.R.m) (hTop : TopMultH R)

theorem cc_eq (b : Bool) (μ : D.what₂.Tup) {j : ℕ} (hj : j < D.R.m) :
    (toChainReal R F tupT hm hTop).CC b μ j = MultT R.θ (R.MY j) (levS _ (R.βY j) (R.datYt (tupT μ) j R.triv))
      (levChi _ (R.βY j) (R.datYt (tupT μ) j R.triv)) := by
  show MultT R.θ (R.MY j) (if j < D.R.m then _ else Set.univ) (if j < D.R.m then _ else 0) = _
  rw [if_pos hj, if_pos hj]

theorem ccp_eq (b : Bool) (μ : D.what₂.Tup) {j : ℕ} (hj : j < D.R.m) :
    (toChainReal R F tupT hm hTop).CCP b μ j = MultT R.θ (R.MY j) (levS _ (R.βY j) (R.datYt (tupT μ) j (R.levR F b)))
      (levChi _ (R.βY j) (R.datYt (tupT μ) j (R.levR F b))) := by
  show MultT R.θ (R.MY j) (if j < D.R.m then _ else Set.univ) (if j < D.R.m then _ else 0) = _
  rw [if_pos hj, if_pos hj]

theorem eec_le (b : Bool) : (toChainReal R F tupT hm hTop).EEc b ≤
    MultT R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.levR F b))) (levChi _ (R.βY 0) (R.dat0 (R.levR F b))) :=
  Submodule.map_mono (goodPart_le R.θ (R.MY 0) _ _ _)

theorem measY (hM : R.IsModels) (t : T) {j : ℕ} (hj : j ≤ D.R.m - 1) (hm : 0 < D.R.m) :
    (R.νY t j).IsHaarMeasure ∧ IsFundamentalDomain (GQ (Yc D j)) (R.fdY t j) (R.νY t j) := by
  by_cases h : j + 1 < D.R.m
  · have := hM.νY t j h
    exact ⟨this.1.1, this.2⟩
  · obtain rfl : j = D.R.m - 1 := by omega
    have := hM.νY' t
    exact ⟨this.1.1, this.2⟩

theorem hermE (hI : Inputs D) (hB : R.BaseW F) (b : Bool) :
    IsHermPos ((toChainReal R F tupT hm hTop).EEc b) ((toChainReal R F tupT hm hTop).ipE b) := by
  have h0 := hB.models.ν0
  have hs := scaled (inv_pos.2 (nP_pos F b)) h0.1.1 h0.2
  exact hermPos_mono (herm_lev hI hB.models.inf (D.sp.Y_sig _) (R.MY 0) (R.βY 0) (R.dat0 (R.levR F b)) hs.1 hs.2)
    (eec_le R F tupT hm hTop b)

theorem isHermPos_chainReal_endSpace_tuple (hI : Inputs D) (hB : R.BaseW F) (b : Bool) (μ : D.what₂.Tup) :
    IsHermPos ((toChainReal R F tupT hm hTop).CC b μ 0) ((toChainReal R F tupT hm hTop).ipE b) := by
  have h0 := hB.models.ν0
  have hs := scaled (inv_pos.2 (nP_pos F b)) h0.1.1 h0.2
  rw [cc_eq R F tupT hm hTop b μ hm]
  exact herm_lev hI hB.models.inf (D.sp.Y_sig _) (R.MY 0) (R.βY 0) (R.datYt (tupT μ) 0 R.triv) hs.1 hs.2

theorem eec_le_cc (b : Bool) (μ : D.what₂.Tup) :
    (toChainReal R F tupT hm hTop).EEc b ≤ (toChainReal R F tupT hm hTop).CC b μ 0 := by
  rw [cc_eq R F tupT hm hTop b μ hm]
  exact (eec_le R F tupT hm hTop b).trans (multT_mono R.θ (R.MY 0) (levS_mono fun x hx =>
    lev_datY_zero rank_lowerChainSpace_zero_le D.R.t (r_le_Y 0) R.Pg (R.Q (tupT μ)) (R.levR F b) R.chi (R.xiR (tupT μ)) x hx))

theorem ccxp_le (b : Bool) (μ : D.what₂.Tup) :
    (toChainReal R F tupT hm hTop).CCXP b μ ≤ (toChainReal R F tupT hm hTop).CCX b μ :=
  multT_mono R.θ R.MX (levS_mono fun x hx =>
    lev_datY_triv D.R.r D.R.t D.R.m r_le_X R.Pg (R.Q (tupT μ)) (R.levR F b) R.chi (R.xiR (tupT μ)) x hx)

theorem hermX (hI : Inputs D) (hB : R.BaseW F) (b : Bool) (μ : D.what₂.Tup) :
    IsHermPos ((toChainReal R F tupT hm hTop).CCX b μ) ((toChainReal R F tupT hm hTop).ipXP b μ) := by
  have h0 := hB.models.νX (tupT μ)
  have hd : 0 < (∏ τ, (Module.finrank ℂ (R.MX.H τ) : ℝ)) / (1 : ℝ) :=
    div_pos (Finset.prod_pos fun τ _ => by exact_mod_cast finrank_model_pos D.sp.X'_sig hI.sp.2 R.MX τ) one_pos
  exact isHermPos_scale (isHermPos_scale (herm_lev hI hB.models.inf D.sp.X'_sig R.MX R.βX (R.datXt (tupT μ)) h0.1.1 h0.2) hd)
    (inv_pos.2 (nP_pos F b))

theorem ccp_le (b : Bool) (μ : D.what₂.Tup) {j : ℕ} (hj : j < D.R.m) :
    (toChainReal R F tupT hm hTop).CCP b μ j ≤ (toChainReal R F tupT hm hTop).CC b μ j := by
  rw [ccp_eq R F tupT hm hTop b μ hj, cc_eq R F tupT hm hTop b μ hj]
  exact multT_mono R.θ (R.MY j) (levS_mono fun x hx =>
    lev_datY_triv D.R.r D.R.t j (r_le_Y j) R.Pg (R.Q (tupT μ)) (R.levR F b) R.chi (R.xiR (tupT μ)) x hx)

theorem hermP (hI : Inputs D) (hB : R.BaseW F) (b : Bool) (μ : D.what₂.Tup) {j : ℕ} (hj : j ≤ D.R.m - 1) :
    IsHermPos ((toChainReal R F tupT hm hTop).CC b μ j) ((toChainReal R F tupT hm hTop).ipP b μ j) := by
  have h0 := measY R hB.models (tupT μ) hj hm
  rw [cc_eq R F tupT hm hTop b μ (by omega)]
  exact isHermPos_scale (herm_lev hI hB.models.inf (D.sp.Y_sig _) (R.MY j) (R.βY j) (R.datYt (tupT μ) j R.triv) h0.1 h0.2)
    (inv_pos.2 (nP_pos F b))

variable (hinj : ∀ i t, Function.Injective (R.extV i t))

theorem holW (i : Fin D.R.m) :
    (toLiftReal R F tupT hm hTop hinj).SW i =
      Mult.parW ((toLiftReal R F tupT hm hTop hinj).W i) ((toLiftReal R F tupT hm hTop hinj).κ i) := by
  have e : sg0 D A = D.what₂.embLL := sgAt_mk _ R.hv0
  show parAt (Wc D i) (sg0 D A) = Mult.parW (Wc D i) (kapAt (Wc D i) (sg0 D A))
  rw [e]
  funext ρ
  unfold parAt Mult.parW
  rw [GlobalTheory.ThetaFiresProbe.lab_fixed, if_pos (GlobalTheory.ThetaFiresProbe.labE_fixed ρ)]

theorem hermW (hI : Inputs D) (hB : R.BaseW F) (i : Fin D.R.m) :
    IsHermPos ((toLiftReal R F tupT hm hTop hinj).Wc i) ((toLiftReal R F tupT hm hTop hinj).ipWc i) := by
  have h0 := hB.models.νW i
  have hs := scaled (inv_pos.2 (nP_pos F false)) h0.1.1 h0.2
  have e : (toLiftReal R F tupT hm hTop hinj).ipWc i = fun x y =>
      ((∏ ρ, ((dimK _ _ (kapAt (Wc D i) (sg0 D A) ρ) : ℚ) : ℝ) : ℝ) : ℂ) *
        ipMT (R.MW i (sg0 D A)) (ENNReal.ofReal (RealDat.nP F false)⁻¹ • R.νW i) (R.fdW i) x y := by
    funext x y
    unfold LiftReal.ipWc
    push_cast
    rfl
  rw [e]
  exact isHermPos_scale (hermPos_mono (herm_lev hI hB.models.inf (D.sp.W_sig _) (R.MW i (sg0 D A)) (R.βW i)
      (R.datWp i (R.levL F false (sg0 D A))) hs.1 hs.2) (Submodule.map_mono (goodPart_le R.θ (R.MW i (sg0 D A)) _ _ _)))
    (Finset.prod_pos fun ρ _ => by exact_mod_cast hI.dim i (sg0 D A) ρ)

theorem hermA (μ : D.what₂.Tup) (i : Fin D.R.m) :
    IsHermPos ((toLiftReal R F tupT hm hTop hinj).Amt μ i) ((toLiftReal R F tupT hm hTop hinj).ipA μ i) :=
  isHermPos_scale (hermPos_mono (isHermPos_ipVia (R.extV i (tupT μ)) (hinj i (tupT μ))) inf_le_left)
    (inv_pos.2 (nP_pos F false))

end Main

theorem spaces_hilbert : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (tupT : D.what₂.Tup → T) (hm : 0 < D.R.m) (hTop : Formalism.IndefR.RecTie.TopMultH R) (hinj : ∀ i t, Function.Injective (R.extV i t)), Inputs D → R.BaseW F → let C := Formalism.IndefR.RecTie.toChainReal R F tupT hm hTop; let L := Formalism.IndefR.RecTie.toLiftReal R F tupT hm hTop hinj; (∀ b, PeterssonHilbertSpace.IsHermPos (C.EEc b) (C.ipE b) ∧ ∀ μ, C.EEc b ≤ C.CC b μ 0 ∧ C.CCXP b μ ≤ C.CCX b μ ∧ PeterssonHilbertSpace.IsHermPos (C.CCX b μ) (C.ipXP b μ) ∧ ∀ j, j ≤ D.R.m - 1 → C.CCP b μ j ≤ C.CC b μ j ∧ PeterssonHilbertSpace.IsHermPos (C.CC b μ j) (C.ipP b μ j)) ∧ (∀ b μ, PeterssonHilbertSpace.IsHermPos (C.CC b μ 0) (C.ipE b)) ∧ (∀ i, L.SW i = Mult.parW (L.W i) (L.κ i) ∧ PeterssonHilbertSpace.IsHermPos (L.Wc i) (L.ipWc i) ∧ ∀ μ, PeterssonHilbertSpace.IsHermPos (L.Amt μ i) (L.ipA μ i)) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F tupT hm hTop hinj hI hB
  exact ⟨fun b => ⟨hermE R F tupT hm hTop hI hB b, fun μ => ⟨eec_le_cc R F tupT hm hTop b μ, ccxp_le R F tupT hm hTop b μ,
      hermX R F tupT hm hTop hI hB b μ, fun j hj => ⟨ccp_le R F tupT hm hTop b μ (by omega), hermP R F tupT hm hTop hI hB b μ hj⟩⟩⟩,
    fun b μ => isHermPos_chainReal_endSpace_tuple R F tupT hm hTop hI hB b μ,
    fun i => ⟨holW R F tupT hm hTop hinj i, hermW R F tupT hm hTop hinj hI hB i, fun μ => hermA R F tupT hm hTop hinj μ i⟩⟩

end GlobalTheory.HilbertLevels
end
