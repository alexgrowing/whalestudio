import Development.WeilBound.ThetaLifts.CartanFactorisation.Kills0Of
import Development.WeilBound.ThetaLifts.CartanFactorisation.KillInf
import Development.WeilBound.ThetaLifts.Reductions.JoinDef
import Development.WeilBound.ThetaLifts.SphericalLattices.ThetaSubSup
import Development.WeilBound.ThetaLifts.SphericalLattices.ProperKilled

noncomputable section

namespace PositivityTheory.Sph

open scoped TensorProduct NNReal Matrix ComplexConjugate
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThK PositivityTheory.ThKF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}
  {B : Base F E} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W} {r q r' q' : ℕ}

theorem killFin3 (hU : Unimod) (hT : ThetaBasic) (hP : PureAct) (hL : LocCpt) (hp : IsPair B M χX χW om r q r' q') {𝓒}
    (hc : Cls B M om 𝓒) (v : Pl F) (hsa : SphAt M B.ψ om v ∨ IrrAt om v) {N}
    (hN : GlobalTheory.Published.ThetaSub om v N) (hNe : N ≠ SB _)
    {f} (hf : f ∈ M.Pol B.ψ B.emb) {φ} (h1 : ∀ u, φ u ∈ SB _) (h2 : ∀ᶠ u in cofinite, φ u = M.vac u)
    (h𝓒 : ∀ x ∈ SB _, pure f (upd φ v x) ∈ 𝓒) (hv : φ v ∈ N) : M.I om (pure f φ) = 0 := by
  classical
  obtain ⟨j, hj, hjS⟩ := intersection_update_fsHerm_neg_one hP hp f h1 h2 v
  obtain ⟨ω, ρ, hω⟩ := PositivityTheory.ThKH.Locrep.locRepEx F E σ n d B X W M om
    ⟨hp.base, ⟨_, _, hp.herm⟩, ⟨_, _, hp.skew⟩, hp.good, ⟨_, _, hp.weil⟩⟩ v
  obtain ⟨hΓ, μ, 𝓕, hμ, h𝓕, hr⟩ := uniW hU hp
  have : BorelSpace (UA σ W.J) := ⟨rfl⟩
  obtain ⟨hinv, hmul, -⟩ := hL F E σ d W v
  have o1 : (1 : UA σ X.J) ∈ UAt σ X (evFin F v) := fun u _ => by simp [mat]
  have o2 : (1 : UA σ W.J) ∈ UAt σ W (evFin F v) := fun u _ => by simp [mat]
  let Q := SB (Fin n × Fin d → Fv F v)
  have jc : ∀ x : Q, j x ∈ 𝓒 := fun x => hj x ▸ h𝓒 x x.2
  let u : Q →ₗ[ℂ] (UA σ W.J → ℂ) :=
    { toFun := fun x => M.I om (j x)
      map_add' := fun x y => by rw [Submodule.coe_add, map_add, I_add' hp hc (jc x) (jc y)]
      map_smul' := fun c x => funext fun h => by
        rw [Submodule.coe_smul, map_smul]; exact PositivityTheory.ThKG.I_smul M om c _ h }
  have hu' : ∀ x, u x = M.I om (j x) := fun _ => rfl
  have uc : ∀ x, Continuous (u x) := fun x => hc.cont _ (jc x)
  have u2 : ∀ x, IntegrableOn (fun g => ‖u x g‖ ^ 2) 𝓕 μ := fun x => hc.sq μ 𝓕 hμ h𝓕 _ (jc x)
    (hj x ▸ Submodule.subset_span ⟨f, hf, _, upd_sb h1 x.2, upd_cof h2 v x, rfl⟩)
  have ui : ∀ x, L2.Inv (ratU σ W.J) (u x) := fun x => I_inv hT hp (hc.sch (jc x))
  have augle : augAt om v ≤ Q := hN.1.trans hN.2.1
  have uaug : ∀ z ∈ augAt om v, M.I om (j z) = 0 := fun z hz => by
    induction hz using Submodule.span_induction with
    | mem z h =>
      obtain ⟨g, hg, x, hx, y, hy, hxy, rfl⟩ := h
      have e : j y = j (y - x) + j x := by rw [← map_add, sub_add_cancel]
      have e2 := I_add' hp hc (jc ⟨y - x, sub_mem hy hx⟩) (jc ⟨x, hx⟩)
      rw [← e, ← hjS _ x hx y hxy, I_left hU hT hp (hc.sch (jc ⟨x, hx⟩))] at e2
      exact (left_eq_add.1 (e2.trans (add_comm _ _)))
    | zero => rw [map_zero]; exact PositivityTheory.ThKG.I_zero M om
    | add a b ha hb iha ihb => rw [map_add, I_add' hp hc (jc ⟨a, augle ha⟩) (jc ⟨b, augle hb⟩), iha, ihb, add_zero]
    | smul c a _ iha => funext h; rw [map_smul, PositivityTheory.ThKG.I_smul, iha]; simp
  rcases hsa with hsa | hsa
  swap
  · have e := (hsa N hN).resolve_right hNe
    have := uaug _ (e ▸ hv)
    rwa [hj, upd_eq] at this
  obtain ⟨s, hs⟩ := hsa ω ρ hω
  obtain ⟨β, hβ, -, -⟩ := exists_beta 𝓕 μ u uc u2
  let A : ∀ h ∈ UAt σ W (evFin F v), Module.End ℂ Q := fun h hh => (ω (1, h)).restrict (hω.pres 1 o1 h hh)
  have hA : ∀ h hh (x : Q), (A h hh x : _ → ℂ) = ω (1, h) x := fun _ _ _ => rfl
  have uA : ∀ h hh x g, u (A h hh x) g = u x (g * h) := fun h hh x g => by
    rw [hu', hu', hA h hh, ← hjS (om (1, h)) x x.2 _ ((hω.acts 1 o1 h hh x x.2 _).2 rfl), I_right]
  have iso : ∀ h hh x y, β (A h hh x) (A h hh y) = β x y := fun h hh x y => by
    simp only [hβ, uA]; exact L2.form_right h𝓕 (ui x) (ui y) h
  have Amul : ∀ h hh h' hh' x, A (h * h') (hmul h hh h' hh') x = A h hh (A h' hh' x) := fun h hh h' hh' x =>
    Subtype.ext (by
      have := hω.mul 1 o1 h hh 1 o1 h' hh' x x.2
      rw [mul_one] at this
      exact this)
  have Aone : ∀ x, A 1 o2 x = x := fun x => Subtype.ext (hω.one x x.2)
  have st := stab_of hω hN
  have sN : s ∉ N := Stab.not_mem hs.gen st hNe
  have bz : ∀ x y : Q, y.1 ∈ augAt om v → β x y = 0 := fun x y hy => by
    rw [hβ, show u y = 0 from (hu' y).trans (uaug _ hy)]; simp
  have bz' : ∀ x y : Q, x.1 ∈ augAt om v → β x y = 0 := fun x y hx => by
    rw [hβ, show u x = 0 from (hu' x).trans (uaug _ hx)]; simp
  let sQ : Q := ⟨s, hs.mem⟩
  have s0 : s ≠ 0 := by
    rintro rfl
    refine hNe (le_antisymm hN.2.1 fun φ hφ => (sup_le hN.1 (Submodule.span_le.2 ?_)) (hs.gen φ hφ))
    rintro _ ⟨h, hh, rfl⟩
    rw [map_zero]
    exact N.zero_mem

  have kA : ∀ y : Q, y.1 ∈ N → β sQ y = 0 := fun y hy => by
    obtain ⟨m, k, w, c, hw, hc⟩ := hs.line y.1 y.2
    have hsum : ∑ i, w i • ω (1, k i) y.1 ∈ N := N.sum_mem fun i _ => N.smul_mem _ (st.2.2 (k i) (hw i).1 y.1 hy)
    have hcs : c • s ∈ N := by
      have := N.sub_mem hsum (hN.1 hc)
      rwa [sub_sub_cancel] at this
    have c0 : c = 0 := by
      by_contra hc0
      have := N.smul_mem c⁻¹ hcs
      rw [smul_smul, inv_mul_cancel₀ hc0, one_smul] at this
      exact sN this
    rw [c0, zero_smul, sub_zero] at hc
    let z : Q := ∑ i, w i • A (k i) (hw i).1 y
    have hz : (z : _ → ℂ) = ∑ i, w i • ω (1, k i) y.1 := by
      simp only [z, Submodule.coe_sum, Submodule.coe_smul, hA]
    have h0 : β sQ z = 0 := bz sQ z (by rw [hz]; exact hc)
    have hk : ∀ i, β sQ (A (k i) (hw i).1 y) = starRingEnd ℂ (w i) * β sQ y := fun i => by
      have e : sQ = w i • A (k i) (hw i).1 sQ := Subtype.ext (by
        rw [Submodule.coe_smul, hA (k i) (hw i).1]; exact ((hw i).2).symm)
      calc β sQ (A (k i) (hw i).1 y) = β (w i • A (k i) (hw i).1 sQ) (A (k i) (hw i).1 y) := by
            rw [← e]
        _ = starRingEnd ℂ (w i) * β sQ y := by
            rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, iso (k i) (hw i).1, smul_eq_mul]
    have e3 : β sQ z = (∑ i, w i * starRingEnd ℂ (w i)) * β sQ y := by
      simp only [z, map_sum, map_smul, hk, smul_eq_mul, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [h0] at e3
    have w0 : w 0 ≠ 0 := fun e => s0 (by
      have := (hw 0).2
      rw [e, zero_smul] at this
      exact this.symm)
    have pos : (0 : ℝ) < ∑ i, Complex.normSq (w i) :=
      lt_of_lt_of_le (Complex.normSq_pos.2 w0)
        (Finset.single_le_sum (fun i _ => Complex.normSq_nonneg (w i)) (Finset.mem_univ 0))
    have hne : (∑ i, w i * starRingEnd ℂ (w i)) ≠ 0 := by
      simp_rw [Complex.mul_conj]
      rw [← Complex.ofReal_sum]
      exact_mod_cast pos.ne'
    exact (mul_eq_zero.1 e3.symm).resolve_left hne

  have kB : ∀ y : Q, y.1 ∈ N → ∀ h (hh : h ∈ UAt σ W (evFin F v)), β (A h hh sQ) y = 0 := fun y hy h hh => by
    have e : A h hh (A h⁻¹ (hinv h hh) y) = y := by
      rw [← Amul h hh h⁻¹ (hinv h hh)]
      simp only [mul_inv_cancel, Aone]
    calc β (A h hh sQ) y = β (A h hh sQ) (A h hh (A h⁻¹ (hinv h hh) y)) := by rw [e]
      _ = β sQ (A h⁻¹ (hinv h hh) y) := iso h hh _ _
      _ = 0 := kA _ (by rw [hA h⁻¹ (hinv h hh)]; exact st.2.2 h⁻¹ (hinv h hh) y.1 hy)

  have kC : ∀ y : Q, y.1 ∈ N → ∀ z : Q, β z y = 0 := fun y hy z => by
    have hle : augAt om v ⊔ Submodule.span ℂ {z | ∃ h ∈ UAt σ W (evFin F v), z = ω (1, h) s} ≤
        (LinearMap.ker (β.flip y)).map Q.subtype := by
      refine sup_le ?_ (Submodule.span_le.2 ?_)
      · intro a ha
        exact ⟨⟨a, augle ha⟩, by rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.flip_apply]; exact bz' _ _ ha, rfl⟩
      · rintro _ ⟨h, hh, rfl⟩
        exact ⟨A h hh sQ, by rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.flip_apply]; exact kB y hy h hh, rfl⟩
    obtain ⟨z', hz', e⟩ := hle (hs.gen z.1 z.2)
    rw [show z = z' from (Subtype.ext e).symm]
    have h0 : β.flip y z' = 0 := hz'
    rwa [LinearMap.flip_apply] at h0
  have key : β ⟨φ v, h1 v⟩ ⟨φ v, h1 v⟩ = 0 := kC _ hv _
  have := L2.eq_zero h𝓕 (uc _) (ui _) (u2 _) ((hβ _ _).symm.trans key)
  rwa [hu', hj, upd_eq] at this

theorem theta_kills_cusp_forms_spherical (hT : ThetaBasic) (hW : WeilConv) (hc : SoCont) (hS : SqInt) (hD : KDecay) (hK : KCoinv) (hC : ICont)
    (hO : ArchOp) (hL : ArchLie) (hQ : ArchUniq) (hAi : RadMax) (hSph : SphTri) (hH : PositivityTheory.ThKR.JoinTri)
    (hSo : SoCoinv) : Kills := by
  intro F E _ _ _ _ _ σ B a a' G X om om' R Rf m
  have p1 := PositivityTheory.ThKG.pairV m.triple
  have p2 := PositivityTheory.ThKG.pairV' m.triple
  have c1 := clsV hW hC hS m.triple
  have c2 := clsV' hD hK hc hC hS m
  have sch : ∀ (f : SInf F _) φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = G.M.vac v) → pure f φ ∈ schA F _ :=
    fun f φ h1 h2 => by
      obtain ⟨g, hg, e⟩ := PositivityTheory.ThKG.pure_eq_pureA p1.good φ h1 h2
      rw [e]
      exact PositivityTheory.ThKG.pureA_mem f hg
  refine ⟨fun f hf φ h1 h2 h => ?_, fun f hf φ h1 h2 h3 h => ?_⟩
  · rcases h with h | ⟨v, h⟩
    · exact killInf' unimodularity_holds hT hO hL hQ exists_maximal_compact_infinite p1 (hAi F E σ B a a' G X om om' m.triple).1 c1 (maxInfP hO hL hQ m).1
        (hH F E σ B a a' G X om om' m.triple).1 h1 h2 (fun f => sch f φ h1 h2) ⟨h, hf⟩
    · exact killFin3 unimodularity_holds hT pureAct local_compact_open_subgroups p1 c1 v (hSph F E σ B a a' G X om om' m.triple v).1
        (maxFinP m v).1.prop.1 (maxFinP m v).1.prop.2 hf h1 h2
        (fun x hx => sch f _ (upd_sb h1 hx) (upd_cof h2 v x)) ⟨h, h1 v⟩
  · rcases h with h | ⟨v, h⟩
    · exact killInf' unimodularity_holds hT hO hL hQ exists_maximal_compact_infinite p2 (hAi F E σ B a a' G X om om' m.triple).2 c2 (maxInfP hO hL hQ m).2
        (hH F E σ B a a' G X om om' m.triple).2 h1 h2
        (fun f => upd_eq φ B.v₁ ▸ pure_soK m.triple f h1 h2 h3) ⟨h, hf⟩
    · by_cases e : v = B.v₁
      · subst e
        have ha := hSo F E σ B a a' G X om om' m.triple _ h3
          ((((hK F E σ B a a' G X om om' R Rf m).1 _ m.triple.chars.good).2.1 _ (h1 _)).1 h)
        obtain ⟨j, hj, hjS⟩ := intersection_update_fsHerm_neg_one pureAct p2 f h1 h2 B.v₁
        have key : ∀ z ∈ augOn om' B.v₁ (G.M'.SoLoc B.ψ B.τ₁), j z ∈ G.M'.So B.ψ B.τ₁ ∧ G.M'.I om' (j z) = 0 := fun z hz => by
          induction hz using Submodule.span_induction with
          | mem z h =>
            obtain ⟨g, hg, x, hx, y, hy, hxy, rfl⟩ := h
            have a1 : j x ∈ G.M'.So B.ψ B.τ₁ := hj x ▸ pure_soK m.triple f h1 h2 (Submodule.subset_span hx)
            have a2 : j y ∈ G.M'.So B.ψ B.τ₁ := hjS _ x hx.1 y hxy ▸ (hK F E σ B a a' G X om om' R Rf m).2 _ _ a1
            have a3 : j (y - x) ∈ G.M'.So B.ψ B.τ₁ := by rw [map_sub]; exact sub_mem a2 a1
            have e2 := I_add' p2 c2 a3 a1
            rw [← map_add, sub_add_cancel, ← hjS _ x hx.1 y hxy, I_left unimodularity_holds hT p2 (c2.sch a1)] at e2
            exact ⟨a3, left_eq_add.1 (e2.trans (add_comm _ _))⟩
          | zero => rw [map_zero]; exact ⟨zero_mem _, PositivityTheory.ThKG.I_zero _ _⟩
          | add a b _ _ iha ihb => rw [map_add, I_add' p2 c2 iha.1 ihb.1, iha.2, ihb.2, add_zero]; exact ⟨add_mem iha.1 ihb.1, rfl⟩
          | smul c a _ iha =>
            rw [map_smul]
            exact ⟨Submodule.smul_mem _ _ iha.1, funext fun h => by rw [PositivityTheory.ThKG.I_smul, iha.2]; simp⟩
        have := (key _ ha).2
        rwa [hj, upd_eq] at this
      · exact killFin3 unimodularity_holds hT pureAct local_compact_open_subgroups p2 c2 v (hSph F E σ B a a' G X om om' m.triple v).2
          (maxFinP m v).2.prop.1 (maxFinP m v).2.prop.2 hf h1 h2
          (fun x hx => upd_eq (upd φ v x) B.v₁ ▸ pure_soK m.triple f (upd_sb h1 hx) (upd_cof h2 v x)
            (by rwa [upd_ne _ _ _ (Ne.symm e)])) ⟨h, h1 v⟩

end PositivityTheory.Sph

end
