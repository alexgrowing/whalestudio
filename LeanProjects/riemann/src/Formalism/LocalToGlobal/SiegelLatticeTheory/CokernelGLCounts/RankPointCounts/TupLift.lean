import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.TupOrb
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.TupGlob
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationLift.DiffIdealNeBot

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.TupLift

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef Formalism.L2.SG.Pf.TupOrb

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

theorem frame_li {T : E} (F : LFlag S r T) (hT : T ≠ 0) : LinearIndependent E (frame F) := by
  show LinearIndependent E (Fin.snoc (α := fun _ => S.V) F.fl.e F.fl.z)
  rw [linearIndependent_finSnoc]
  refine ⟨F.fl.e_indep, fun hz => ?_⟩
  have h0 : ∀ x ∈ Submodule.span E (Set.range F.fl.e), S.hT x F.fl.z = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, rfl⟩ := hy
      exact F.fl.z_orth a
    | zero => simp
    | add x y _ _ hx hy => simp [map_add, hx, hy]
    | smul c x _ hx => simp [hx]
  have := h0 _ hz
  rw [F.fl.z_norm] at this
  exact hT (neg_eq_zero.1 this)

theorem nlam_frame_locP {g : ℕ} {Λ : Submodule (𝓞 E) S.V} {T' : E} {F₁ : LFlag S r T'}
    (hL : IsLift Λ F₁) (hC : IsFixedConv Λ g F₁) {m : S.V ≃ₗ[E] S.V} (hm : m ∈ NLam Λ F₁)
    (P : HeightOneSpectrum (𝓞 E)) (hg : (g : 𝓞 E) ∈ P.asIdeal) (b : Fin (r + 1)) :
    m (frame F₁ b) ∈
      (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Submodule.span (𝓞 E) (Set.range (frame F₁)))) := by
  have := P.isPrime
  have hA : Formalism.L2.SG.Pf.Apart Λ F₁ ≤
      Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Submodule.span (𝓞 E) (Set.range (frame F₁))) := by
    refine sup_le ?_ ?_
    · exact Formalism.L2.SG.Pf.Act.xlam_le_locP Λ g hC P hg (fun a =>
        Formalism.L2.SG.Pf.le_locP' _ _ (Submodule.subset_span ⟨a.castSucc, Formalism.L2.SG.Pf.frame_castSucc_td F₁ a⟩))
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact Formalism.L2.SG.Pf.le_locP' _ _
        (Submodule.subset_span ⟨Fin.last _, (Formalism.L2.SG.Pf.frame_last_td F₁).trans hL.2.symm⟩)
  have h0 := Formalism.L2.SG.Pf.frame_mem_locP_Apart hL hC P hg b
  have h1' : m (frame F₁ b) ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Formalism.L2.SG.Pf.Apart Λ F₁) := by
    rw [← Formalism.L2.SG.Pf.NLam_Apart hm hL, Formalism.L2.SG.Pf.gmap_locP]
    exact (Formalism.L2.SG.Pf.gmap_apply_mem m _ _).2 h0
  exact Formalism.L2.SG.Pf.locP_le_locP' hA h1'

theorem coef_int {g : ℕ} {Λ : Submodule (𝓞 E) S.V} {T' : E} {F₁ : LFlag S r T'} (hT : T' ≠ 0)
    (hL : IsLift Λ F₁) (hC : IsFixedConv Λ g F₁) {m : S.V ≃ₗ[E] S.V} (hm : m ∈ NLam Λ F₁)
    {U : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (hU : ∀ b, m (frame F₁ b) = ∑ c, U c b • frame F₁ c)
    (P : HeightOneSpectrum (𝓞 E)) (hg : (g : 𝓞 E) ∈ P.asIdeal) (b : Fin (r + 1)) :
    ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ ∀ c, ∃ o : 𝓞 E, (s : E) * U c b = (o : E) := by
  have := P.isPrime
  obtain ⟨s, hs, hsm⟩ := nlam_frame_locP hL hC hm P hg b
  obtain ⟨o, ho⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).1 hsm
  refine ⟨s, hs, fun c => ⟨o c, ?_⟩⟩
  have hli := frame_li F₁ hT
  have h1 : ∑ c, ((s : E) * U c b) • frame F₁ c = (s : E) • m (frame F₁ b) := by
    rw [hU b, Finset.smul_sum]
    simp only [mul_smul]
  have h2 : ∑ c, ((o c : 𝓞 E) : E) • frame F₁ c = (s : E) • m (frame F₁ b) := by
    rw [← Formalism.L2.SG.Pf.smul_O, ← ho]
    simp only [Formalism.L2.SG.Pf.smul_O]
  have hsum : ∑ c, ((s : E) * U c b - (o c : E)) • frame F₁ c = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, h1, h2, sub_self]
  exact sub_eq_zero.1 ((Fintype.linearIndependent_iff.1 hli) _ hsum c)

theorem modG_lift {g : ℕ} {Λ : Submodule (𝓞 E) S.V} {T T' : E} {F : LFlag S r T} {F₁ : LFlag S r T'}
    (hT : T' ≠ 0) (hL : IsLift Λ F₁) (hC : IsFixedConv Λ g F₁) (hFΛ : ∀ c, frame F c ∈ Λ)
    {ν m : S.V ≃ₗ[E] S.V} (hν : IsAutLam S Λ ν) (hm : m ∈ NLam Λ F₁)
    {U U' : Matrix (Fin (r + 1)) (Fin (r + 1)) E}
    (hνF : ∀ b, ν (frame F b) = ∑ c, U c b • frame F c) (hmF : ∀ b, m (frame F₁ b) = ∑ c, U' c b • frame F₁ c)
    (hTie : ∀ P : HeightOneSpectrum (𝓞 E), (g : 𝓞 E) ∈ P.asIdeal → ∀ c b, ∃ s : 𝓞 E, s ∉ P.asIdeal ∧
      ∃ o : 𝓞 E, (s : E) * (U c b - U' c b) = (g : E) * o)
    (h1 : ∀ c, ModG S Λ g (frame F₁ c - frame F c)) (b : Fin (r + 1)) :
    ModG S Λ g (ν⁻¹ (m (frame F₁ b)) - frame F b) := by
  intro P hg
  have := P.isPrime
  have key : m (frame F₁ b) - ν (frame F b) ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {(g : 𝓞 E)} • Λ) := by
    rw [hmF b, hνF b, ← Finset.sum_sub_distrib]
    refine Submodule.sum_mem _ (fun c _ => ?_)
    have e : U' c b • frame F₁ c - U c b • frame F c =
        U' c b • (frame F₁ c - frame F c) + (U' c b - U c b) • frame F c := by
      rw [smul_sub, sub_smul]; abel
    rw [e]
    refine Submodule.add_mem _ ?_ ?_
    · obtain ⟨s, hs, ho⟩ := coef_int hT hL hC hm hmF P hg b
      obtain ⟨o, hoc⟩ := ho c
      obtain ⟨t, ht, htx⟩ := h1 c P hg
      refine ⟨t * s, P.asIdeal.primeCompl.mul_mem ht hs, ?_⟩
      have eq : (t * s) • (U' c b • (frame F₁ c - frame F c)) = o • (t • (frame F₁ c - frame F c)) := by
        rw [Formalism.L2.SG.Pf.smul_O, Formalism.L2.SG.Pf.smul_O, Formalism.L2.SG.Pf.smul_O, smul_smul, smul_smul]
        congr 1
        push_cast
        rw [← hoc]
        ring
      rw [eq]
      exact Submodule.smul_mem _ o htx
    · obtain ⟨s, hs, o, ho⟩ := hTie P hg c b
      refine ⟨s, hs, ?_⟩
      have eq : s • ((U' c b - U c b) • frame F c) = -(o • ((g : 𝓞 E) • frame F c)) := by
        rw [Formalism.L2.SG.Pf.smul_O, Formalism.L2.SG.Pf.smul_O, Formalism.L2.SG.Pf.smul_O, smul_smul, smul_smul, ← neg_smul]
        congr 1
        have : (s : E) * (U' c b - U c b) = -((s : E) * (U c b - U' c b)) := by ring
        rw [this, ho]
        push_cast
        ring
      rw [eq]
      exact Submodule.neg_mem _ (Submodule.smul_mem _ o
        (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) (hFΛ c)))
  have hinv : IsAutLam S Λ ν⁻¹ := Formalism.L2.SG.Pf.isAutLam_inv hν
  have e : ν⁻¹ (m (frame F₁ b)) - frame F b = ν⁻¹ (m (frame F₁ b) - ν (frame F b)) := by
    rw [map_sub]
    simp [LinearEquiv.coe_inv]
  rw [e]
  have eN : Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {(g : 𝓞 E)} • Λ) =
      Formalism.HermitianLatticesTheory.gmap ν⁻¹ (Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {(g : 𝓞 E)} • Λ)) := by
    rw [← Formalism.L2.SG.Pf.gmap_locP, Formalism.L2.SG.Pf.gmap_ideal_smul, hinv.2]
  rw [eN]
  exact (Formalism.L2.SG.Pf.gmap_apply_mem ν⁻¹ _ _).2 key

theorem zhat_lift {T T' : E} (F : LFlag S r T) (F₁ : LFlag S r T') {ν m : S.V ≃ₗ[E] S.V}
    (hiso : ∀ x y, S.hT (ν x) (ν y) = S.hT x y) {U U' : Matrix (Fin (r + 1)) (Fin (r + 1)) E}
    (hνF : ∀ b, ν (frame F b) = ∑ c, U c b • frame F c) (hmF : ∀ b, m (frame F₁ b) = ∑ c, U' c b • frame F₁ c)
    (a b : Fin (r + 1)) :
    S.hT (frame F a) (ν⁻¹ (m (frame F₁ b))) = (U.conjTranspose * ZhatL F F₁ * U') a b := by
  have e : S.hT (frame F a) (ν⁻¹ (m (frame F₁ b))) = S.hT (ν (frame F a)) (m (frame F₁ b)) := by
    rw [← hiso (frame F a) (ν⁻¹ (m (frame F₁ b)))]
    simp [LinearEquiv.coe_inv]
  rw [e, hνF a, hmF b]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, ZhatL, Zhat, brS, map_sum, map_smulₛₗ,
    LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum, starRingEnd_apply]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  simp only [RingHom.id_apply]
  ring

end Gen

section D7

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def NLamOnto : Prop :=
  ∀ (D : D7) (w : D.what₂.Word) (G : FlagG (VS D) D.R.rS ((Tu D w : ℕ) : D.host.E))
    (Λ : Submodule (𝓞 D.host.E) (VS D).V),
    IsRowLat D G Λ → Tu D w ≠ 0 → ∀ U : PairVal.MatR D, IsUpUni U → TupGlob.IntFr U →
      ∃ ν ∈ NLam Λ (lf D G), ∀ b, ν (frame (lf D G) b) = ∑ c, U c b • frame (lf D G) c

variable {D : D7}

theorem isRowLat_of_pd {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
    {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hΛ : IsRowLat D F0 Λ)
    {F₁ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)} (hp : PD D Λ (lf D F0) u' F₁) :
    IsRowLat D F₁.fl Λ :=
  ⟨hΛ.1, ⟨hΛ.2.1.1, hΛ.2.1.2.1, ⟨hp.1.1, rfl⟩, hp.2.2.1⟩, hp.2.2.2⟩

theorem repAtTup_of (M : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, Formalism.MainNotions.S.Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (δ : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word)
    (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))
    (hG : TupGlob.GlobMove D M δ u u') (hO : NLamOnto) : FibPart.RepAtTup M δ u u' F0 what₂ := by
  intro hpre γ w hGw Z hZ hel htup
  have hΛ : IsRowLat D F0 γ.lam := hpre.2.2.2.2.1.1 γ.lam γ.mem
  have hrel : γ.relevant := hpre.2.2.2.2.2 γ w hel
  obtain ⟨x, hx⟩ := hpre.2.2.2.1 γ w hel.2 hrel hel.1.1
  have hex : ∃ y : Point D.host.E (D.R.rS + 1) × LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E) ×
      PairVal.MatR D × PairVal.MatR D, PairVal.NormRep γ y.1 y.2.1 y.2.2.1 y.2.2.2 :=
    ⟨(w, x.1, x.2.1, x.2.2), hx⟩
  have hz : LsDatumB.zT γ = ZhatL (lf D F0) hex.choose.2.1 := by
    simp only [LsDatumB.zT, LsDatumB.nrep, dif_pos hex]
  have hspec := hex.choose_spec
  generalize hex.choose = y at hz hspec
  obtain ⟨w₁, F₁, L₁, U₁⟩ := y
  obtain ⟨⟨p₁, e₁⟩, hadm₁, -⟩ := hspec
  simp only at hz
  have hEq := Formalism.L2.SG.Closed.TermEqIff_holds D u u' F0 γ.lam hΛ
  have hFun := Formalism.L2.SG.Closed.TermFun_holds D u u' F0 γ.lam hΛ
  obtain ⟨Fa, ⟨pa, ea⟩, hGa, hcell⟩ := hel.2
  have hdca := (hEq ⟨Fa, pa⟩ ⟨F₁, p₁⟩).1 (ea.trans e₁.symm)
  have hG₁ : Gval (lf D F0) F₁ ≠ 0 := by rw [Formalism.L2.SG.Pf.gval_rel (lf D F0) hdca]; exact hGa
  have hcell₁ : IsInCell (ZhatOM (ZhatL (lf D F0) F₁)) w := (hFun.2.1 ⟨Fa, pa⟩ ⟨F₁, p₁⟩ hdca w).1 hcell
  obtain ⟨Fg, ⟨pg, eg⟩, hgen⟩ := hel.1.1
  have hgen₁ : IsGeneric γ.lam (gS D) (lf D F0) F₁ :=
    (hFun.2.2.2.1 ⟨Fg, pg⟩ ⟨F₁, p₁⟩ ((hEq ⟨Fg, pg⟩ ⟨F₁, p₁⟩).1 (eg.trans e₁.symm))).1 hgen
  have hAt₁ : PCount.AtMat w (ZhatL (lf D F0) F₁) := hcell₁
  have htup' : ∀ p, PCount.tupZ M δ u u' (ZhatL (lf D F0) F₁) p = PCount.tupZ M δ u u' Z p := fun p => by
    rw [← hz]; exact congrFun htup p
  obtain ⟨U, U', hU, hU', hiU, hiU', htie, hZeq⟩ := hG w _ Z hGw hAt₁ hZ htup'
  obtain ⟨ν, hν, hνF⟩ := hO D u F0 γ.lam hΛ hpre.2.2.1.1.ne_zero U hU hiU
  obtain ⟨m, hm, hmF⟩ := hO D u' F₁.fl γ.lam (isRowLat_of_pd hΛ p₁) hpre.2.2.1.2.2.1.ne_zero U' hU' hiU'
  have hm' : m ∈ NLam γ.lam F₁ := hm
  have hmF' : ∀ b, m (frame F₁ b) = ∑ c, U' c b • frame F₁ c := hmF
  have hAut : IsAutLam (VS D) γ.lam (ν⁻¹ * m) :=
    Formalism.L2.SG.Pf.isAutLam_mul (Formalism.L2.SG.Pf.isAutLam_inv hν.1) hm.1
  let F2 := Formalism.L2.SG.Saturated.mapL (ν⁻¹ * m) hAut.1 F₁
  have hf2 : ∀ b, frame F2 b = ν⁻¹ (m (frame F₁ b)) := fun b => by
    rw [Formalism.L2.SG.Saturated.frame_mapL]; rfl
  have hdc : DCRel γ.lam (lf D F0) F₁ F2 :=
    ⟨ν⁻¹, Formalism.L2.SG.Pf.nlamPf_inv hν, m, hm', hf2, rfl⟩
  have pd2 : PD D γ.lam (lf D F0) u' F2 :=
    Formalism.L2.SG.Closed.TermStable_holds D u u' F0 γ.lam hΛ ⟨F₁, p₁⟩ F2 hdc
  have hT' : ((Tu D u' : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hpre.2.2.1.2.2.1.ne_zero
  have hFΛ : ∀ c, frame (lf D F0) c ∈ γ.lam := by
    intro c
    refine Fin.lastCases ?_ (fun a => ?_) c
    · rw [Formalism.L2.SG.Pf.frame_last_td]; exact hΛ.2.1.2.2.1.1
    · rw [Formalism.L2.SG.Pf.frame_castSucc_td]; exact PI.NRL.e_mem_lam D F0 γ.lam hΛ a
  have hiso : ∀ x y, (VS D).hT (ν x) (ν y) = (VS D).hT x y :=
    ((Formalism.L2.SG.Pf.isAutLam_iff γ.lam ν).1 hν.1).1
  have hent : ∀ a b, (VS D).hT (frame (lf D F0) a) (frame F2 b) =
      (U.conjTranspose * ZhatL (lf D F0) F₁ * U') a b := fun a b => by
    rw [hf2 b]; exact zhat_lift (lf D F0) F₁ hiso hνF hmF' a b
  refine ⟨F2, ⟨⟨pd2.1, pd2.2.1, ?_⟩, ?_, ?_, pd2.2.2, ?_⟩,
    pd2, (Quot.sound (show TermDef.Rel γ.lam (lf D F0) (PD D γ.lam (lf D F0) u') ⟨F₁, p₁⟩ ⟨F2, pd2⟩ from hdc)).symm.trans e₁⟩
  · rw [Formalism.L2.SG.Pf.gval_rel (lf D F0) hdc]; exact hG₁
  · refine ⟨fun a b hab => Matrix.one_apply_ne (ne_of_lt hab).symm, fun a => Matrix.one_apply_eq a, fun b => ?_⟩
    rw [frameAct_one', hf2 b]
    exact modG_lift hT' p₁.1 p₁.2.2.1 hFΛ hν.1 hm' hνF hmF' htie
      (fun c => by have := hadm₁.2.2 c; rwa [frameAct_one'] at this) b
  · exact (hFun.2.2.2.1 ⟨F₁, p₁⟩ ⟨F2, pd2⟩ hdc).1 hgen₁
  · have hZZ : ZhatL (lf D F0) F2 = U.conjTranspose * ZhatL (lf D F0) F₁ * U' := by
      funext a b
      exact hent a b
    rw [hZeq]
    exact hZZ

end D7

end Formalism.L2.SG.Pf.TupLift
