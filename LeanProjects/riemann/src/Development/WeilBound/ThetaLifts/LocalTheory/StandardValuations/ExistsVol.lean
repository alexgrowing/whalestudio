import Development.WeilBound.ThetaLifts.LocalTheory.StandardValuations.ConeVal
import Development.WeilBound.ThetaLifts.LocalTheory.StandardValuations.SmallFSing
import Development.WeilBound.ThetaLifts.LocalTheory.UnramifiedDeterminedBySpherical
import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.SplitCharacterFacts
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.ResCardAndUniformizer
import Development.AbelianVarietyTheory.Definitions.Foundations.SecondCountableAndT2LocalField

noncomputable section

namespace PositivityTheory.ThKG.Std

open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SplitFlip Matrix
open PositivityTheory.KCo PositivityTheory.ThK.SplitDict PositivityTheory.ThKG.StdDict PositivityTheory.ThKG.Loc MeasureTheory ValuativeRel Topology GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl F}
  {t : E →ₐ[F] Fv F v} {sec : Fv F v × Fv F v → AE F E}

open PositivityTheory.ThK.SplitLoc

local instance measFv (v : Pl F) : MeasurableSpace (Fv F v) := borel _

local instance borelFv (v : Pl F) : BorelSpace (Fv F v) := ⟨rfl⟩

local instance scFv (v : Pl F) : SecondCountableTopology (Fv F v) := (GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := Fv F v)).1

theorem exists_vol (v : Pl F) : ∃ m : Measure (Fv F v), IsVol m :=
  ⟨Measure.addHaarMeasure ⟨⟨_, IsNonarchimedeanLocalField.isCompact_closedBall _ (valuation (Fv F v) 1)⟩, by
    rw [(isClopen_ball one_ne_zero).2.interior_eq]; exact ⟨0, by simp⟩⟩, inferInstance, Measure.addHaarMeasure_self⟩

def skF {n n₁ : ℕ} (h : n = n₁ + 2) (i₀ i₁ : ℕ) (j : Fin n₁) : Fin n := ⟨skip i₀ i₁ j, by
  have := j.2; unfold skip; split_ifs <;> omega⟩

theorem skF_inj {n n₁ : ℕ} (h : n = n₁ + 2) (i₀ i₁ : ℕ) : Function.Injective (skF h i₀ i₁) := fun a b e => Fin.ext (by
  have := congrArg Fin.val e
  simp only [skF, skip] at this
  split_ifs at this <;> omega)

theorem skF_cover {n n₁ : ℕ} (h : n = n₁ + 2) {j₀ j₁ : Fin n} (l : j₀.1 < j₁.1) (i : Fin n) :
    i = j₀ ∨ i = j₁ ∨ ∃ j, i = skF h j₀ j₁ j := by
  have := i.2
  have := j₁.2
  by_cases a : i.1 = j₀.1
  · exact Or.inl (Fin.ext a)
  by_cases b : i.1 = j₁.1
  · exact Or.inr (Or.inl (Fin.ext b))
  refine Or.inr (Or.inr ?_)
  by_cases c : i.1 < j₀.1
  · exact ⟨⟨i.1, by omega⟩, Fin.ext (by simp [skF, skip, c])⟩
  by_cases d : i.1 < j₁.1
  · exact ⟨⟨i.1 - 1, by omega⟩, Fin.ext (by simp only [skF, skip]; split_ifs <;> omega)⟩
  · exact ⟨⟨i.1 - 2, by omega⟩, Fin.ext (by simp only [skF, skip]; split_ifs <;> omega)⟩

theorem skF_ne {n n₁ : ℕ} (h : n = n₁ + 2) {j₀ j₁ : Fin n} (l : j₀.1 < j₁.1) (j : Fin n₁) :
    skF h j₀ j₁ j ≠ j₀ ∧ skF h j₀ j₁ j ≠ j₁ := by
  constructor <;> intro e <;> have := congrArg Fin.val e <;> simp only [skF, skip] at this <;> split_ifs at this <;> omega

theorem skF_mid (b : ℕ) : skF (rfl : b + 2 = b + 2) (0 : Fin (b + 2)).1 (Fin.last (b + 1)).1 = mid := funext fun j => Fin.ext (by
  have := j.2
  show skip 0 (b + 1) j = j + 1
  unfold skip; split_ifs <;> omega)

variable {B : Base F E}

theorem plane' (hσ : IsCMExt F E σ) {n n₁ : ℕ} {X : Spc F E n} {X₁ : Spc F E n₁} {H : Plane E n n₁} {j₀ j₁ : Fin n}
    (h : H.IsAdapted σ B X X₁ j₀ j₁) {ε : E} (hJ : ∀ i j, σ (X.J j i) = ε * X.J i j) (hε : ε * ε = 1) (w : B.P) (l : j₀.1 < j₁.1) :
    PE σ (B.τ w) X.J X₁.J (X.bas w) (X₁.bas w) H.ι (skF h.rank j₀ j₁) ∧ PX σ (B.τ w) X.J (X.bas w) H.x H.y j₀ j₁ (B.τ w ε) :=
  plane hσ h hJ hε w rfl rfl (fun _ => rfl) (skF_inj _ _ _) (skF_cover _ l) (fun e => by rw [e] at l; omega)
    (fun j => (skF_ne _ l j).1) fun j => (skF_ne _ l j).2

theorem cond_ex {ν : (Fv F v)ˣ →* ℂˣ} (h : ∃ e, CondLE (unifAt v) e ν) (hr : ¬ GlobalTheory.SplitWeil.IsUnram ν) :
    ∃ κ, condExp ν = κ + 1 ∧ CondLE (unifAt v) (κ + 1) ν ∧ ¬ CondLE (unifAt v) κ ν := by
  have m : CondLE (unifAt v) (condExp ν) ν := Nat.sInf_mem h
  have h0 : condExp ν ≠ 0 := fun e => hr fun x hx => by
    rw [e] at m
    exact m x ⟨hx, by simpa using (valuation (Fv F v)).map_sub_le hx.le (map_one _).le⟩
  obtain ⟨κ, hκ⟩ := Nat.exists_eq_succ_of_ne_zero h0
  exact ⟨κ, hκ, by rw [hκ] at m; exact m, fun e => Nat.notMem_of_lt_sInf (s := {c | CondLE (unifAt v) c ν}) (by
    show κ < condExp ν
    omega) e⟩

theorem eps_eq {m : Measure (Fv F v)} (hm : IsVol m) {ψ : AddChar (AF F) ℂ} (hψ : IsPsi (psiV ψ v)) {ν : (Fv F v)ˣ →* ℂˣ} {κ : ℕ}
    (h : condExp ν = κ + 1) (hν : CondLE (unifAt v) (κ + 1) ν) (z : ℕ) :
    gI m (psiV ψ v) ν (((unifAt v : Fv F v) ^ (κ + 1))⁻¹) * (ν (unifAt v) : ℂ) ^ (κ + 1) *
      ((GlobalTheory.SplitWeil.resCard (Fv F v) : ℂ) ^ (κ + 1)) ^ z = eps ψ ν (1 - z) := by
  have q := (GlobalTheory.CompanionTheory.IdxAd.Unif.resCard_and_uniformizer F v).1
  have q0 : (Ideal.absNorm v.asIdeal : ℂ) ≠ 0 := by exact_mod_cast Ideal.absNorm_eq_zero_iff.not.2 v.ne_bot
  have g : gI m (psiV ψ v) ν (((unifAt v : Fv F v) ^ condExp ν)⁻¹) =
      ((GlobalTheory.SplitWeil.resCard (Fv F v) : ℂ) ^ condExp ν)⁻¹ * gauss ψ ν := by
    letI : Fintype (Res (Fv F v) (condExp ν))ˣ := Fintype.ofFinite _
    rw [gI_gauss (ϖ := unifAt v) hm hψ exists_isUnif.choose_spec (by omega) (h ▸ hν), gauss]
    congr
    exact Subsingleton.elim _ _
  rw [eps, ← h, g, q, show -(condExp ν : ℤ) * (1 - z) = (condExp ν * z : ℕ) - (condExp ν : ℕ) by push_cast; ring, zpow_sub₀ q0,
    zpow_natCast, zpow_natCast, pow_mul]
  ring

theorem data {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om om' R Rf} (T : IsMatched B G X om om' R Rf) (w : B.P) (hw : w.1 ∈ X.T)
    {sec} (h : IsSec σ (B.τ w) sec) {κ : ℕ} (hν : CondLE (unifAt w.1) (κ + 1) (chrW X.ν (B.τ w))) :
    ∃ ι ι' φ φ', Lin G.M B.ψ w (cW (B.τ w) (G.V.bas w) (G.W.bas w)) (cB σ (B.τ w) G.V G.W (G.V.bas w) (G.W.bas w)) ι ∧
      Lin G.M' B.ψ w (cB σ (B.τ w) G.V' G.W (G.V'.bas w) (G.W.bas w)) (fun u => -cW (B.τ w) (G.V'.bas w) (G.W.bas w) u) ι' ∧
      φ ∈ SB _ ∧ φ' ∈ SB _ ∧ ι φ = std (chrW X.ν (B.τ w)) (unifAt w.1) (κ + 1) (eA a a') ∧
      ι' φ' = std (chrW X.ν (B.τ w)) (unifAt w.1) (κ + 1) (eB a a') ∧ Rf.p w φ = Rf.p' w φ' ∧ Rf.p w φ ≠ 0 ∧
      (∀ K, IsStab B K → ∀ k ∈ kAt K (evFin F w), Acts (evFin F w) (om (k, 1)) φ φ) ∧
      ∀ K, IsStab B K → ∀ k ∈ kAt K (evFin F w), Acts (evFin F w) (om' (k, 1)) φ' φ' := by
  have t := T.triple
  have hB := t.base
  obtain ⟨m, hm⟩ := exists_vol w.1
  have hu := hB.psiP w w.2
  obtain ⟨hα, hβ, e, hcond, hram, -⟩ := PositivityTheory.ThK.SplitAsm.split_character_facts F E B X a a' w (B.τ w) t.chars
  have hS : HidaSetting a a' (unifAt w.1) (chrW X.α (B.τ w)) (chrW X.β (B.τ w)) (chrW X.ν (B.τ w)) :=
    ⟨exists_isUnif.choose_spec, hα, hβ, e, t.geo.lt, t.geo.even, hcond⟩
  obtain ⟨ι, ι', l, l', v1, v2, z⟩ := T.fin.zeta w hw
  have L := local_splitting_linear_skew hB.std h (grams h t.geo.hV t.geo.hW) l v1
  have L' := lin_Bar hB.std h (grams h t.geo.hV' t.geo.hW) l' v2
  obtain ⟨φ, s, a1⟩ := L.bij.2.2 (std_mem hS.unif (by omega) hν (eA a a'))
  obtain ⟨φ', s', a2⟩ := L'.bij.2.2 (std_mem hS.unif (by omega) hν (eB a a'))
  refine ⟨ι, ι', φ, φ', L, L', s, s', a1, a2, (z φ s φ' s').2 ?_, fun h0 => ?_, fun K hK k hk => ?_, fun K hK k hk => ?_⟩
  · rw [a1, a2]; exact std_pair hS (hram hw) (by omega) hν
  · have := (z φ s 0 (zero_mem _)).1 (by rw [h0, map_zero])
    rw [a1, map_zero] at this
    refine pRam_ne (a' := a') (β := chrW X.β (B.τ w)) hS.unif (this.trans ?_)
    funext g; simp [smallP, smallF]
  · obtain ⟨j, l1, u1, g1, -⟩ := model_alt hB t.geo.hV t.geo.hW (t.geo.hM.vac w) t.weil (t.geo.hV.bas w) (t.geo.hW.bas w)
      (ν := chrW X.ν (B.τ w)) (β := chrW X.β (B.τ w)) (MonoidHom.ext fun x => by
        rw [chrW_div, chrW_conj hB.cm _ t.chars.resα, chrW_conj hB.cm _ t.chars.resβ, Chars.ν, chrW_div, inv_div_inv])
      (chrW_conj hB.cm _ t.chars.resβ)
    have J := local_splitting_linear_skew hB.std h (grams h t.geo.hV t.geo.hW) l1 u1
    obtain ⟨φ₁, b1, b2, b3⟩ := g1 k (uat_closure hk.2) φ s
    rw [lin_uniq hm hB hu t.geo.hM L J s, a1, omA_std (inB_mem h (t.geo.hV.bas w) hK hk.1), ← a1, lin_uniq hm hB hu t.geo.hM L J b1] at b3
    rwa [L.bij.2.1 b1 s b3] at b2
  · obtain ⟨j, l1, u1, g1, -⟩ := model_Bar hB t.geo.hV' t.geo.hW (t.geo.hM'.vac w) t.weil' (t.geo.hV'.bas w) (t.geo.hW.bas w)
      (δ := 1) (fun x => by rw [one_mul]; exact hu x) (one_smul _ _).symm
    have J := lin_Bar hB.std h (grams h t.geo.hV' t.geo.hW) l1 u1
    obtain ⟨φ₁, b1, b2, b3⟩ := g1 k (uat_closure hk.2) φ' s'
    rw [lin_uniq hm hB hu t.geo.hM' L' J s', a2] at b3
    erw [omB_std (inB_mem h (t.geo.hV'.bas w) hK hk.1)] at b3
    erw [← a2] at b3
    rw [lin_uniq hm hB hu t.geo.hM' L' J b1] at b3
    rwa [L'.bij.2.1 b1 s' b3] at b2

theorem nu_data {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om om'} (t : IsTriple B G X om om') (w : B.P) (hw : w.1 ∈ X.T) :
    (∀ x, chrW X.ν ((B.τ w).comp σ) x = (chrW X.ν (B.τ w) x)⁻¹) ∧ ∃ κ, condExp (chrW X.ν (B.τ w)) = κ + 1 ∧
      CondLE (unifAt w.1) (κ + 1) (chrW X.ν (B.τ w)) ∧ ¬ CondLE (unifAt w.1) κ (chrW X.ν (B.τ w)) := by
  obtain ⟨-, -, e, ⟨c, h1, h2⟩, hram, -⟩ := PositivityTheory.ThK.SplitAsm.split_character_facts F E B X a a' w (B.τ w) t.chars
  refine ⟨fun x => ?_, cond_ex ⟨c, e ▸ h1.div h2⟩ (hram hw)⟩
  rw [Chars.ν, chrW_div, chrW_div, chrW_conj t.base.cm _ t.chars.resα, chrW_conj t.base.cm _ t.chars.resβ, inv_div_inv, inv_div]

theorem eA_val {a a' : ℕ} (i : Fin a) : (eA a a' i).1 = i := rfl

theorem eB_val {a a' : ℕ} (i : Fin a') : (eB a a' i).1 = a + i := rfl

theorem unit_J {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (h : IsSec σ t sec) {r s r' s'} (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s') :
    IsUnit (X.J.map t) ∧ IsUnit (W.J.map t) := by
  have := grams h hX hW
  rw [← incM_map h, ← incM_map h]
  exact ⟨this.uA, this.uB⟩

theorem stdB : StdB := by
  refine ⟨1, fun F E _ _ _ _ _ σ B a b G G₁ H H' cf e ei ev e' ei' ev' he hl he' hl' K μ hK hμ X om om' R Rf om₁ om₁' R₁ Rf₁ T T₁ w hw => ?_⟩
  have t := T.triple
  have t₁ := T₁.triple
  have hB := t.base
  obtain ⟨m, hm⟩ := exists_vol w.1
  have hu := hB.psiP w w.2
  have hϖ : IsUnif (unifAt w.1) := exists_isUnif.choose_spec
  obtain ⟨⟨sec, h⟩, -⟩ := section_statement F E σ hB.cm w (B.τ w)
  obtain ⟨hc, κ, k1, k2, k3⟩ := nu_data t w hw
  obtain ⟨ι, ι', φ, φ', L, L', s, s', a1, a2, mt, -, -, fx⟩ := data T w hw h k2
  obtain ⟨ι₁, ι₁', φ₁, φ₁', L₁, L₁', s₁, s₁', b1, b2, mt₁, ne₁, -, -⟩ := data T₁ w hw h k2
  have lt : (eB a (b + 2) 0).1 < (eB a (b + 2) (Fin.last _)).1 := by simp [eB_val]
  obtain ⟨pe', px'⟩ := plane' hB.cm (j₀ := eB a (b + 2) 0) (j₁ := eB a (b + 2) (Fin.last _)) cf.hH' (ε := -1)
    (fun i j => by rw [t.geo.hW.skew, neg_one_mul]) (by simp) w lt
  obtain ⟨pe, px⟩ := plane' hB.cm (j₀ := 0) (j₁ := Fin.last _) cf.hH (ε := 1) (fun i j => by rw [t.geo.hV'.herm, one_mul]) (by simp) w
    (by simp)
  rw [map_neg, map_one] at px'
  rw [map_one] at px
  have cv := skF_cover (rfl : b + 2 = b + 2) (j₀ := 0) (j₁ := Fin.last _) (by simp)
  rw [skF_mid] at pe cv
  have cv' := skF_cover cf.hH'.rank lt
  have nz := skF_ne cf.hH'.rank lt
  set jc := skF cf.hH'.rank (eB a (b + 2) 0) (eB a (b + 2) (Fin.last _)) with hjc
  have e1 : ev w φ = ((((GlobalTheory.SplitWeil.resCard (Fv F w) : ℂ) ^ (κ + 1))⁻¹) ^ a) • φ₁ := by
    refine L₁.bij.2.1 ((hl.vac w).2 ▸ Submodule.mem_map_of_mem s) ((SB _).smul_mem _ s₁) (funext fun y => ?_)
    rw [ev0W hm hB hu h t.geo.hM t₁.geo.hM he hl L L₁ (unit_J h t.geo.hV t.geo.hW).1 (by rw [cf.eV]; exact pe_one _ _) pe' px' cv' s,
      a1, map_smul, b1]
    exact int_ev hm hϖ (skF_inj _ _ _) (fun i => Fin.ext (by simp [hjc, skF, skip, eA_val, eB_val])) _
      (fun ⟨i, hi⟩ => by have := congrArg Fin.val hi; have := i.2; simp [eA_val, eB_val] at *; omega) (fun j => (nz j).1.symm) y
  let P : Finset (Fin (b + 2) × Fin (a + (b + 2))) :=
    Finset.univ.filter fun p => p.1 = Fin.last _ ∨ p.2 = eB a (b + 2) (Fin.last _) ∧ p.1 ≠ 0
  have hP : ∀ p, p ∈ P ↔ p.1 = Fin.last _ ∨ p.2 = eB a (b + 2) (Fin.last _) ∧ p.1 ≠ 0 := fun p => by simp [P]
  have ml : ∀ i : Fin b, mid i ≠ Fin.last (b + 1) := fun i h => by have := congrArg Fin.val h; simp [mid] at this; omega
  have ei2 : Function.Injective (eB a (b + 2)) := fun _ _ h => by simpa using finSumFinEquiv.injective h
  have e2 := cone_val hm hB hu L' L₁' (hl'.vac w).2 (fun φ s y => evB hm hB hu h t.geo.hM' t₁.geo.hM' he' hl' L' L₁'
      (unit_J h t₁.geo.hV' t₁.geo.hW).1 (unit_J h t.geo.hV' t.geo.hW).2 pe px cv pe' px' cv' P hP s y) hϖ X.ν hc k2 k3 s' s₁' a2 b2 hμ
    (fx K hK) (shiftB_c h px px') (skF_inj _ _ _) ei2
    (fun i => Fin.ext (by have := i.2; show skip (a + 0) (a + (b + 1)) (a + i) = a + (i + 1)
                          unfold skip; split_ifs <;> omega))
    (fun j => (nz j).1.symm) (fun j => (nz j).2.symm) (fun i j => by simp [hP, ml, (nz j).2]) (by simp [hP]) (by simp [hP])
    (Or.inl ⟨fun j _ => by simp [hP], fun i => by simp [hP, ml, ei2.eq_iff]⟩) (fun j => (Fin.last _, eA a (b + 2) j))
    (fun _ _ h => by simpa [eA] using h) (fun p => by
      rw [hP]
      refine ⟨?_, fun ⟨x, y⟩ => ?_⟩
      · rintro ⟨j, rfl⟩
        exact ⟨Or.inl rfl, fun ⟨i, hi⟩ => by simpa using finSumFinEquiv.injective hi⟩
      · obtain ⟨j | j, hj⟩ := finSumFinEquiv.surjective p.2
        · exact ⟨j, Prod.ext (x.resolve_right fun x => y ⟨_, x.1.symm⟩).symm hj⟩
        · exact absurd ⟨j, hj⟩ y) ((a - (b + 2)) / 2 + 1)
  have q0 : (GlobalTheory.SplitWeil.resCard (Fv F w) : ℂ) ≠ 0 := by
    rw [(GlobalTheory.CompanionTheory.IdxAd.Unif.resCard_and_uniformizer F w).1]; exact_mod_cast Ideal.absNorm_eq_zero_iff.not.2 w.1.ne_bot
  refine ⟨φ, s, φ', s', mt, ?_, ?_⟩
  · rw [e1, map_smul]; exact smul_ne_zero (by positivity) ne₁
  · rw [e2, e1, eps_eq hm (isPsi hB.std hu) k1 k2, map_smul, map_smul, mt₁, smul_smul]
    simp

theorem stdA_gen {b a' : ℕ} {G : Geo σ (b + 2) a'} {G₁ : Geo σ b a'} {H : Plane E (b + 2) b} {H' : Plane E (b + 2 + a') (b + a')}
    (eV : G₁.V' = G.V') (hH : H.IsAdapted σ B G.V G₁.V 0 (b + 1)) (hH' : H'.IsAdapted σ B G.W G₁.W 0 (b + 1))
    {e ei ev e' ei' ev'} (he : IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e) (hl : IsEvLoc G.M G₁.M e ei ev)
    (he' : IsEv B G.M' G₁.M' 1 H'.ι (iso0 a' H') e') (hl' : IsEvLoc G.M' G₁.M' e' ei' ev') {K : Subgroup (UA σ G.V.J)} {μ : LocMeas K}
    (hK : IsStab B K) (hμ : μ.Is) {X om om' R Rf om₁ om₁' R₁ Rf₁} (T : IsMatched B G X om om' R Rf)
    (T₁ : IsMatched B G₁ X om₁ om₁' R₁ Rf₁) (w : B.P) (hw : w.1 ∈ X.T) :
    ∃ φ ∈ SB _, ∃ φ' ∈ SB _, Rf.p w φ = Rf.p' w φ' ∧ Rf₁.p' w (ev' w φ') ≠ 0 ∧
      Rf₁.p w (coneF B G.M om μ w (ev w) (shiftA H H') X.ν ((b + 2 - a') / 2) φ) =
        eps B.ψ (chrW X.ν (B.τ w)) (1 - (((b + 2 - a') / 2 : ℕ) : ℤ)) • Rf₁.p' w (ev' w φ') := by
  have t := T.triple
  have t₁ := T₁.triple
  have hB := t.base
  obtain ⟨m, hm⟩ := exists_vol w.1
  have hu := hB.psiP w w.2
  have hϖ : IsUnif (unifAt w.1) := exists_isUnif.choose_spec
  obtain ⟨⟨sec, h⟩, -⟩ := section_statement F E σ hB.cm w (B.τ w)
  obtain ⟨hc, κ, k1, k2, k3⟩ := nu_data t w hw
  obtain ⟨ι, ι', φ, φ', L, L', s, s', a1, a2, mt, -, fx, -⟩ := data T w hw h k2
  obtain ⟨ι₁, ι₁', φ₁, φ₁', L₁, L₁', s₁, s₁', b1, b2, mt₁, ne₁, -, -⟩ := data T₁ w hw h k2
  have lt : (eA (b + 2) a' 0).1 < (eA (b + 2) a' (Fin.last _)).1 := by simp [eA_val]
  obtain ⟨pe', px'⟩ := plane' hB.cm (j₀ := eA (b + 2) a' 0) (j₁ := eA (b + 2) a' (Fin.last _)) hH' (ε := -1)
    (fun i j => by rw [t.geo.hW.skew, neg_one_mul]) (by simp) w lt
  obtain ⟨pe, px⟩ := plane' hB.cm (j₀ := 0) (j₁ := Fin.last _) hH (ε := 1) (fun i j => by rw [t.geo.hV.herm, one_mul]) (by simp) w
    (by simp)
  rw [map_neg, map_one] at px'
  rw [map_one] at px
  have cv := skF_cover (rfl : b + 2 = b + 2) (j₀ := 0) (j₁ := Fin.last _) (by simp)
  rw [skF_mid] at pe cv
  have cv' := skF_cover hH'.rank lt
  have nz := skF_ne hH'.rank lt
  set jc := skF hH'.rank (eA (b + 2) a' 0) (eA (b + 2) a' (Fin.last _)) with hjc
  have e1 : ev' w φ' = ((((GlobalTheory.SplitWeil.resCard (Fv F w) : ℂ) ^ (κ + 1))⁻¹) ^ a') • φ₁' := by
    refine L₁'.bij.2.1 ((hl'.vac w).2 ▸ Submodule.mem_map_of_mem s') ((SB _).smul_mem _ s₁') (funext fun y => ?_)
    rw [ev0B hm hB hu h t.geo.hM' t₁.geo.hM' he' hl' L' L₁' (unit_J h t.geo.hV' t.geo.hW).1 (by rw [eV]; exact pe_one _ _) pe' px' cv' s',
      a2, map_smul, b2]
    exact int_ev hm hϖ (skF_inj _ _ _) (fun i => Fin.ext (by
        show skip 0 (b + 1) (b + i) = b + 2 + i
        unfold skip; split_ifs <;> omega)) _
      (fun ⟨i, hi⟩ => by simpa using finSumFinEquiv.injective hi) (fun j => (nz j).2.symm) y
  let P : Finset (Fin (b + 2) × Fin (b + 2 + a')) :=
    Finset.univ.filter fun p => p.2 = eA (b + 2) a' 0 ∨ p.1 = 0 ∧ p.2 ≠ eA (b + 2) a' (Fin.last _)
  have hP : ∀ p, p ∈ P ↔ p.2 = eA (b + 2) a' 0 ∨ p.1 = 0 ∧ p.2 ≠ eA (b + 2) a' (Fin.last _) := fun p => by simp [P]
  have m0 : ∀ i : Fin b, mid i ≠ 0 := fun i h => by simpa [mid] using congrArg Fin.val h
  have ei2 : Function.Injective (eA (b + 2) a') := fun _ _ h => by simpa using finSumFinEquiv.injective h
  have e2 := cone_val hm hB hu L L₁ (hl.vac w).2 (fun φ s y => evA hm hB hu h t.geo.hM t₁.geo.hM he hl L L₁
      (unit_J h t.geo.hV t.geo.hW).1 (unit_J h t₁.geo.hV t₁.geo.hW).2 pe px cv pe' px' cv' P hP s y) hϖ X.ν hc k2 k3 s s₁ a1 b1 hμ
    (fx K hK) (shiftA_c h px px') (skF_inj _ _ _) ei2
    (fun i => Fin.ext (by have := i.2; show skip 0 (b + 1) i = i + 1
                          unfold skip; split_ifs <;> omega))
    (fun j => (nz j).1.symm) (fun j => (nz j).2.symm) (fun i j => by simp [hP, m0, (nz j).1]) (by simp [hP]) (by simp [hP, ei2.eq_iff])
    (Or.inr ⟨fun i hi => by simp [hP, hi, ei2.eq_iff], fun j => by simp [hP, m0, ei2.eq_iff]⟩) (fun j => (0, eB (b + 2) a' j))
    (fun _ _ h => by simpa [eB] using h) (fun p => by
      rw [hP]
      refine ⟨?_, fun ⟨x, y⟩ => ?_⟩
      · rintro ⟨j, rfl⟩
        exact ⟨Or.inr ⟨rfl, fun hi => by simpa using finSumFinEquiv.injective hi⟩,
          fun ⟨i, hi⟩ => by simpa using finSumFinEquiv.injective hi⟩
      · obtain ⟨j | j, hj⟩ := finSumFinEquiv.surjective p.2
        · exact absurd ⟨j, hj⟩ y
        · exact ⟨j, Prod.ext (x.resolve_left fun x => y ⟨_, x.symm⟩).1.symm hj⟩) ((b + 2 - a') / 2)
  have q0 : (GlobalTheory.SplitWeil.resCard (Fv F w) : ℂ) ≠ 0 := by
    rw [(GlobalTheory.CompanionTheory.IdxAd.Unif.resCard_and_uniformizer F w).1]; exact_mod_cast Ideal.absNorm_eq_zero_iff.not.2 w.1.ne_bot
  refine ⟨φ, s, φ', s', mt, ?_, ?_⟩
  · rw [e1, map_smul, ← mt₁]; exact smul_ne_zero (by positivity) ne₁
  · rw [e2, e1, eps_eq hm (isPsi hB.std hu) k1 k2, map_smul, map_smul, mt₁, smul_smul]

theorem stdA : StdA :=
  ⟨1, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cf _ _ _ _ _ _ he hl he' hl' _ _ hK hμ _ _ _ _ _ _ _ _ _ T T₁ w hw => by
    simpa only [map_one, Units.val_one, one_mul] using stdA_gen cf.eV cf.hH cf.hH' he hl he' hl' hK hμ T T₁ w hw⟩

end PositivityTheory.ThKG.Std
