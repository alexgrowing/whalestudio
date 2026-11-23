import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockOfApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistCharacterOfArtin
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSubgroupIsUnit
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LargeCoefficientFieldContainsTwistValues
import Formalism.LocalToGlobal.Columns.RowFormsSel
import Formalism.LocalToGlobal.UnitaryNorms.RamificationIdxEqOneOfNotDvd

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.PlaceRead.TupAt

section General

open Formalism.IndefR Formalism.IndefR.Links Formalism.L2.DIV GlobalTheory.SeriesTie Formalism.ConjugateSelfDual ReciprocityTheory.Gal

variable {D : D7}

theorem splitK_of_prime (P : PlE D.host) (hp : (Ideal.absNorm P.asIdeal).Prime)
    (hn : ¬ Ideal.absNorm P.asIdeal ∣ 30 * D.host.condN) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ D.host.cls p = .splitK ∧ ((p : 𝓞 D.host.E) ∈ P.asIdeal) := by
  have := P.isPrime
  have h2 : Ideal.absNorm P.asIdeal = normV P := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
  have h1 : P.asIdeal.inertiaDeg ℤ = 1 :=
    Nat.Prime.eq_one_of_pow (Ideal.absNorm_pow_inertiaDeg (P.asIdeal.under ℤ) P.asIdeal ▸ hp)
  have key : ∀ r : ℕ, r.Prime → ((r : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal → Ideal.absNorm P.asIdeal = r := fun r hr hm => by
    by_contra hne
    have hc : IsCoprime ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 D.host.E) (r : 𝓞 D.host.E) :=
      Nat.Coprime.cast ((Nat.coprime_primes hp hr).2 hne)
    obtain ⟨a, b, e⟩ := hc
    exact this.ne_top ((Ideal.eq_top_iff_one _).2
      (e ▸ add_mem (Ideal.mul_mem_left _ _ (Ideal.absNorm_mem _)) (Ideal.mul_mem_left _ _ hm)))
  have hN : ¬ Ideal.absNorm P.asIdeal ∣ D.host.condN := fun h => hn (h.mul_left _)
  have hF : Fact (Ideal.absNorm P.asIdeal).Prime := ⟨hp⟩
  have hsp := Formalism.L2.Host.span_isPrime (Ideal.absNorm P.asIdeal)
  have hmax : (Ideal.span {((Ideal.absNorm P.asIdeal : ℕ) : ℤ)}).IsMaximal :=
    hsp.isMaximal (by rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hp.ne_zero)
  have hlo : P.asIdeal.LiesOver (Ideal.span {((Ideal.absNorm P.asIdeal : ℕ) : ℤ)}) := by
    refine ⟨hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_⟩
    rw [Ideal.span_singleton_le_iff_mem, Ideal.under_def, Ideal.mem_comap, map_natCast]
    exact Ideal.absNorm_mem _
  refine GlobalTheory.TwistDet.exists_splitK h1 (Formalism.L2.Host.ramificationIdx_eq_one D.host _ hN P.asIdeal) ?_
    (fun h => Formalism.HC.HostRaw.ne_q_of_not_dvd hN (key _ D.host.hyp.1 h))
    (fun h => Formalism.HC.HostRaw.ne_d_of_not_dvd hN (key _ D.host.hyp.2.1 h))
  rw [← h2]
  exact hp.eq_two_or_odd'.resolve_left (Formalism.HC.HostRaw.ne_two_of_not_dvd hN)

theorem isDelta_delAt (cf : CharFrame D) (i : D.ntw.Tw) : ∃ q : ℕ, IsDelta q (cf.delAt (D.ntw.l i)) ∧
    (∀ P : Pl D.host.E, P ∈ D.ntw.pD i ↔ (q : 𝓞 D.host.E) ∈ P.asIdeal) ∧ (q = D.host.pde ∨ q = D.host.pde') := by
  refine ⟨if D.ntw.l i = D.host.pde then D.host.pde' else D.host.pde, ?_, fun P => ?_, ?_⟩
  · unfold CharFrame.delAt
    split_ifs
    exacts [cf.isDel', cf.isDel]
  · rw [← Finset.mem_coe, D.ntw.pD_eq]
    rfl
  · split_ifs
    exacts [Or.inr rfl, Or.inl rfl]

theorem ram_mul (cf : CharFrame D) (i : D.ntw.Tw) {Q : Finset (Pl D.host.E)} {ψ : HChar D.host.E} (hψ : IsPsi (D.ntw.l i) Q ψ)
    (P : Pl D.host.E) : ¬ (cf.delAt (D.ntw.l i) * ψ).UnrAt P ↔ P ∈ D.ntw.pD i ∨ P ∈ Q := by
  obtain ⟨q, hδ, hq, -⟩ := isDelta_delAt cf i
  have hm : ∀ x, (cf.delAt (D.ntw.l i) * ψ).loc P x = (cf.delAt (D.ntw.l i)).loc P x * ψ.loc P x := fun _ => rfl
  by_cases hP : P ∈ D.ntw.pD i
  · refine iff_of_true (fun hu => ?_) (Or.inl hP)
    obtain ⟨a, ha⟩ := hψ.ord
    have h15 := (hδ.ine P ((hq P).1 hP) (D.ntw.l i ^ a)).1 fun x hx => by
      have h3 : ψ.loc P x ^ (D.ntw.l i ^ a) = 1 :=
        (MonoidHom.pow_apply ..).symm.trans (congrArg (fun χ : HChar D.host.E => χ.loc P x) ha)
      rw [eq_inv_of_mul_eq_one_left ((hm x).symm.trans (hu x hx)), inv_pow, h3, inv_one]
    have hl : (D.ntw.l i).Prime := (D.ntw.lPrime _).out
    have h3 := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hl).1 (Nat.prime_three.dvd_of_dvd_pow (dvd_trans (by norm_num) h15))
    have h5 := (Nat.prime_dvd_prime_iff_eq Nat.prime_five hl).1 (Nat.prime_five.dvd_of_dvd_pow (dvd_trans (by norm_num) h15))
    omega
  · have hd := hδ.unr P fun h => hP ((hq P).2 h)
    rw [or_iff_right hP, ← not_iff_not, not_not, ← hψ.ram]
    exact forall₂_congr fun x hx => by rw [hm, hd x hx, one_mul]

theorem chrEq_twVia {cf : CharFrame D} {c : NChoice D} {tp : TupTied D cf c} (h : PsiChoiceCompatible D cf c tp) {w : D.what₂.places.Pl}
    (hw : D.what₂.muAt w ≠ D.what₂.mu0) (hψ : IntegralHeckeForms.TwOK (c.twI w) (c.k' w) (c.Q w) (chr c w)) {ρ : Setup D.ntw} (hρ : ρ.Good)
    (hv : ∀ P, P ∉ c.Q w → P ∉ D.ntw.pD (c.twI w) → ∃ y, D.what₂.embLL y = (((tp.psi w).val P : ℂˣ) : ℂ))
    (ι : KE c w →+* ℂ) (hι : ∀ y, ι (c.embW w y) = D.what₂.embLL y) : ChrEq (twVia ρ ι).chi (tp.psi w) := by
  classical
  obtain ⟨-, -, hopen, -, hzk, -, -⟩ := hψ
  have hl : D.ntw.l (c.twI w) ≠ 0 := (D.ntw.lPrime _).out.ne_zero
  have hz : D.ntw.zk (c.twI w) (c.k' w) ^ (D.ntw.l (c.twI w) ^ c.k' w) = 1 :=
    Units.ext (by simpa using (D.ntw.zk_prim (c.twI w) (c.k' w)).pow_eq_one)
  have hfin := GlobalTheory.TwistChr.finite_placesOver D.host.E (l := D.what₂.places.resChar w) (c.twI_l w ▸ hl)
  refine GlobalTheory.TwistChr.chrEq_charOf hρ.rc _ _ hopen (pow_ne_zero (c.k' w) hl) (fun σ => ?_) _
    ((c.Q w ∪ D.ntw.pD (c.twI w)) ∪ hfin.toFinset)
    (fun v hv => ((tp.psi_is w hw).ram v).2 fun hQ => hv (Finset.mem_union_left _ (Finset.mem_union_left _ hQ)))
    fun v hv' A hA σ hσ => ?_
  · obtain ⟨m, hm⟩ := hzk σ
    rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz, one_zpow]
  · have h1 : v ∉ c.Q w := fun hQ => hv' (Finset.mem_union_left _ (Finset.mem_union_left _ hQ))
    obtain ⟨y, hy⟩ := hv v h1 fun hQ => hv' (Finset.mem_union_left _ (Finset.mem_union_right _ hQ))
    have hy' : D.what₂.embLL y⁻¹ = (((tp.psi w).val v)⁻¹ : ℂˣ).1 := by rw [map_inv₀, hy, Units.val_inv_eq_inv_val]
    have e := h w hw v h1 (fun hQ => hv' (Finset.mem_union_right _ (hfin.mem_toFinset.2 hQ))) A σ hA hσ _ hy'
    rw [← hy', ← hι, e, ← IsScalarTower.algebraMap_apply]
    rfl

variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {Rl : RealDat3 D A3 Ks} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd}

theorem isTupOf {μ0 : T0} (hL : Rl.toRealDat.toLevCh.Is μ0) {ρ : Setup D.ntw} (hρ : ρ.Good) (hp : RealPin Rl cG ρ) (i : D.ntw.Tw)
    (j : Fin D.R.m) (b : Bool) {Q : Finset (Pl D.host.E)} {ψ : HChar D.host.E} (hψ : IsPsi (D.ntw.l i) Q ψ) {t : T0}
    (ht : Rl.xiH t = Rl.C.delAt (D.ntw.l i) * ψ) (hch : ∀ P ∈ Rl.Q t, P ∈ ρ.ch i) (τ : GlobalTheory.ExportSeries.Twist D Circle)
    (hc : ChrEq τ.chi ψ) (hQ : τ.Q = half (ρ.ch i) Q) : GlobalTheory.ConjTwist.IsTupOf Rl.toRealDat (ρ.B i j b) τ t := by
  classical
  refine ⟨GlobalTheory.ChrEqUnique.idc_unique D _ _ _ (hL.xi t) (ht ▸ GlobalTheory.TwistChr.chrEq_mul (hp.delta i j b) hc), ?_⟩
  have key : ∀ P, (P ∈ Rl.Q t ∨ ∃ P' ∈ Rl.Q t, Lev.IsConjPl P' P) ↔ P ∈ D.ntw.pD i ∨ P ∈ Q := fun P =>
    (hL.Q_ram t P).symm.trans (ht ▸ ram_mul Rl.C i hψ P)
  ext P
  rw [Finset.mem_union, hρ.delta, hQ]
  refine Iff.trans ?_ (or_congr mem_half mem_half).symm
  rw [← or_and_right, ← key]
  refine ⟨fun h => ⟨Or.inl h, hch P h⟩, fun ⟨h1, h2⟩ => h1.elim id fun ⟨P', h3, h4⟩ => ?_⟩
  by_cases e : P' = P
  · exact e ▸ h3
  · exact absurd h2 (((hρ.ch i).pair _ _ (GlobalTheory.BigOn.Exp.isConjPl_of_lev h4) e).1 (hch P' h3))

end General

theorem val_delAt {D : D7} {cf : CharFrame D} (h : ValLL0 D cf) (i : D.ntw.Tw) (P : PlE D.host) (hP : P ∉ D.ntw.pD i) :
    ∃ y, D.what₂.embLL y = (((cf.delAt (D.ntw.l i)).val P : ℂˣ) : ℂ) := by
  obtain ⟨q, hδ, hq, -⟩ := isDelta_delAt cf i
  have hu := hδ.unr P fun e => hP ((hq P).2 e)
  have hv : (cf.delAt (D.ntw.l i)).ValuesIn 0 D.what₂.embLL := by
    unfold CharFrame.delAt
    split_ifs
    exacts [h.toLL.del', h.toLL.del]
  obtain ⟨y, hy⟩ := hv P hu
  exact ⟨y, by simpa [HChar.valTw] using hy⟩

section State

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}
  (x : St P)

theorem mem_Wt {v : B.places.Pl} (hv : TwistedAt (Dof x) v) : v ∈ P.Wt := by_contra fun h => hv (P.q.mu.off v h)

theorem tupT_muTw {v : B.places.Pl} (hv : TwistedAt (Dof x) v) :
    x.r.Y.tupT ((Dof x).what₂.muTw v) = x.m.z.R.mu ((Dof x).plEq v) := by
  rw [← ((Dof x).what₂.muAt_or v).resolve_left hv, x.r.Y.muAt v, x.r.Y.tupT_tup]

theorem xi_mu (ch : NChoice (Dof x)) {v : B.places.Pl} (hv : TwistedAt (Dof x) v) {ψ : HChar (Dof x).host.E} (e : ψ = T.psi v) :
    x.m.z.R.xiH (x.m.z.R.mu ((Dof x).plEq v)) = x.m.z.R.C.delAt ((Dof x).ntw.l (ch.twI v)) * ψ := by
  have h1 := (x.m.z.mu v).2
  rw [if_pos (mem_Wt x hv)] at h1
  refine ((x.m.z.lev.xiH _).trans h1).trans ?_
  refine Eq.trans ?_ (congrArg₂ (· * ·) (congrArg₂ CharFrame.delAt x.m.z.lev.C (ch.twI_l v)) e).symm
  rfl

end State

theorem isTupOf_tupT_muTw_of_embW_eq : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AllSt fun _ _ _ T w P x => ∀ (l : StrictHenselianAcyclic hL x) (ch : NChoice (Dof x)) (tp : TupTied (Dof x) (cfOf x) ch), tp.xi = w.I.xi → tp.psi = T.psi → ch.Q = QOf P → (∀ v, TwistedAt (Dof x) v → ch.k' v = T.k v) → ChoiceSide (Dof x) (cfOf x) l.mt.M l.b.Bs.exp ch tp → ∀ v, TwistedAt (Dof x) v → IntegralHeckeForms.TwOK (ch.twI v) (ch.k' v) (ch.Q v) (GlobalTheory.PlaceRead.chr ch v) →
  IntegralHeckeForms.ClsQ (D := Dof x) (ch.Q v) ∧ ∀ (j : Fin (Dof x).R.m) (ι : GlobalTheory.PlaceRead.KE ch v →+* ℂ), (∀ y, ι (ch.embW v y) = (Dof x).what₂.embLL y) →
    GlobalTheory.ConjTwist.IsTupOf x.m.z.R.toRealDat (l.b.ser.ex.ρ.B (ch.twI v) j (ch.sd v)) (GlobalTheory.PlaceRead.twVia l.b.ser.ex.ρ ι) (x.r.Y.tupT ((Dof x).what₂.muTw v)) := by
  intro _ hL
  have s1 : Step KPx (fun _ _ _ _ => True) _ := Step.of_evLgG (evLgG_of_evLg GlobalTheory.Mem.R3.OkVals.large_coefficientField_contains_twist_values)
  refine s1.trans (Step.of_all ?_)
  intro K B f T _ _ _ hOk w _ P x l ch tp _ hpsi _ _ side v hv hok
  have hV : ValsIn w.I := (hOk w.px w.I P.hX w.ok w.C_eq w.xi_range).1
  clear hOk s1
  have hψ : IsPsi ((Dof x).ntw.l (ch.twI v)) (ch.Q v) (tp.psi v) := by
    have h := tp.psi_is v hv
    rw [← ch.twI_l v] at h
    exact h
  have he : tp.psi v = T.psi v := congrFun hpsi v
  have ht := xi_mu x ch hv he
  have hr := fun PP => ram_mul x.m.z.R.C (ch.twI v) hψ PP
  rw [← ht] at hr
  refine ⟨fun PP hP => ?_, fun j ι hι => ?_⟩
  · obtain ⟨-, h1, -, h2⟩ := (T.psi_tw v).2.2.2 PP fun hu => (hψ.ram PP).1 (he ▸ hu :) hP
    exact splitK_of_prime (D := Dof x) PP h1 fun hd => h2 (Or.inl hd)
  · rw [tupT_muTw x hv]
    refine isTupOf x.m.z.lev.is l.b.ser.ex.good l.b.ser.ex.pin _ j _ hψ ht (fun PP hP => ?_) _ ?_ rfl
    · have hs : IsSplitPl (Dof x).host PP := by
        rcases (hr PP).1 ((x.m.z.lev.is.Q_ram _ PP).2 (Or.inl hP)) with h | h
        · obtain ⟨q, -, hq, e⟩ := isDelta_delAt x.m.z.R.C (ch.twI v)
          have h' := (hq PP).1 h
          refine l.a.elem.split PP (e.imp (fun e => ?_) fun e => ?_) <;> subst e <;> exact h'
        · exact hψ.split PP h
      refine (l.b.ser.ch _ PP hs).2 ?_
      obtain ⟨u, -, e⟩ := (Formalism.L2.Col.mem_QE _ _ _).1 ((x.m.z.lev.Q _).le hP)
      exact l.sel.ge ⟨u, e⟩
    · refine chrEq_twVia side.psi hv hok l.b.ser.ex.good (fun PP h1 h2 => ?_) ι hι
      have hval : ValLL0 (Dof x) x.m.z.R.C := by rw [x.m.z.lev.C]; exact l.a.val
      obtain ⟨y, hy⟩ := val_delAt hval _ PP h2
      have hx := x.m.z.lev.xiH (x.m.z.R.mu ((Dof x).plEq v))
      obtain ⟨z, hz⟩ := hV.1 _ PP (hx ▸ not_not.1 fun hu => ((hr PP).1 hu).elim h2 h1 :)
      have hz' : (Dof x).what₂.embLL z = (((x.m.z.R.C.delAt ((Dof x).ntw.l (ch.twI v)) * tp.psi v).val PP : ℂˣ) : ℂ) :=
        hz.trans (congrArg (fun χ : HChar (Dof x).host.E => ((χ.val PP : ℂˣ) : ℂ)) (hx.symm.trans ht))
      refine ⟨y⁻¹ * (show (Dof x).what₂.LL from z), ?_⟩
      rw [map_mul, map_inv₀, hy]
      refine (congrArg _ hz').trans ?_
      rw [HChar.val_mul, Units.val_mul, inv_mul_cancel_left₀ (Units.ne_zero _)]

end GlobalTheory.PlaceRead.TupAt

end
