import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalToGlobal.IndefiniteReal.RhoGeo
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFormsFiniteDimensionalOf
import Formalism.LocalToGlobal.ProjectiveLattices.ThProps
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCharacterEmbeddingCompatStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryEqRealMulFiniteSplit
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.OrthonormalBaseFrameNeg
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelGroupActionEqZeroOfNoLift

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompAct

open ReciprocityTheory.ChartRestriction.G.FD

theorem exists_action {H G C : Type} [Group H] [Group G] (comp : H → C) (hs : ∀ x, ∃ h, comp h = x)
    (Lift : G → H → Prop) (hex : ∀ g, ∃ k, Lift g k) (h1 : Lift 1 1)
    (hmul : ∀ g g' k k', Lift g k → Lift g' k' → Lift (g * g') (k * k'))
    (key : ∀ g k k' h h', Lift g k → Lift g k' → comp h = comp h' → comp (h * k) = comp (h' * k')) :
    ∃ mv : C → G → C, (∀ x, mv x 1 = x) ∧ (∀ x g g', mv x (g * g') = mv (mv x g) g') ∧ (∀ x, ∃ h, comp h = x) ∧
      ∀ g k, Lift g k → ∀ h, comp (h * k) = mv (comp h) g := by
  choose rep hrep using hs
  choose l hl using hex
  have main : ∀ g k, Lift g k → ∀ h, comp (h * k) = comp (rep (comp h) * l g) :=
    fun g k hk h => key g k (l g) h _ hk (hl g) (hrep _).symm
  refine ⟨fun x g => comp (rep x * l g), fun x => ?_, fun x g g' => ?_, fun x => ⟨rep x, hrep x⟩, main⟩
  · have := main 1 1 h1 (rep x)
    rw [mul_one, hrep] at this
    exact this.symm
  · show comp (rep x * l (g * g')) = comp (rep (comp (rep x * l g)) * l g')
    rw [← main g' (l g') (hl g'), mul_assoc]
    exact key (g * g') _ _ _ _ (hl _) (hmul _ _ _ _ (hl g) (hl g')) rfl

theorem frame_calc {n : Type} [Fintype n] [DecidableEq n] (x B P Q P' M : Matrix n n ℂ) (hy : (B * x).det ≠ 0)
    (h1 : M * B = B * Q) (h2 : P * Q = P') : P * x * ((B * x)⁻¹ * M * (B * x)) = P' * x := by
  have hx : IsUnit x.det := by
    rw [Matrix.det_mul] at hy
    exact (right_ne_zero_of_mul hy).isUnit
  have e : M * (B * x) = (B * x) * (x⁻¹ * (Q * x)) := by
    rw [← Matrix.mul_assoc M, h1, Matrix.mul_assoc B x, Matrix.mul_nonsing_inv_cancel_left _ _ hx, Matrix.mul_assoc]
  rw [Matrix.mul_assoc _ M, e, Matrix.nonsing_inv_mul_cancel_left _ _ hy.isUnit, Matrix.mul_assoc,
    Matrix.mul_nonsing_inv_cancel_left _ _ hx, ← Matrix.mul_assoc, h2]

variable {D : D7} {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}

theorem archM_mul (V : HSp D) (hr : V.rank = r) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (g g' : GA D V) :
    Matrix.reindex (finCongr hr) (finCongr hr) (archM V θ g) * Matrix.reindex (finCongr hr) (finCongr hr) (archM V θ g') =
      Matrix.reindex (finCongr hr) (finCongr hr) (archM V θ (g * g')) := by
  have e : archM V θ (g * g') = archM V θ g * archM V θ g' := by
    unfold archM
    rw [map_mul, Units.val_mul, Matrix.map_mul]
  rw [e]
  exact Matrix.submatrix_mul_equiv _ _ _ (finCongr hr).symm _

theorem coset_of_comp_eq {V : HSp D} {X : Comp → Data E r} {dict : GA D V → Σ k, Frame (X k).Ψ r}
    {Kf : Subgroup (GA D V)} {th : ∀ c, (X c).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {hr : V.rank = r}
    (hd : DictIsUnif V dict Kf th hr) (x₀ : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (hf : ∀ h, ∃ p : GA D V, ∀ τ : (X (dict h).1).Ψ, mat (dict h).2 τ =
      Matrix.reindex (finCongr hr) (finCongr hr) (archM V (th (dict h).1 τ) p) * x₀ τ.1)
    {h h' : GA D V} (e : (dict h).1 = (dict h').1) :
    ∃ a ∈ GinfC V, ∃ γ ∈ GQ V, ∃ k ∈ Kf, h * a = γ * h' * k := by
  obtain ⟨-, -, ⟨x0, h0, h3⟩, -, -, h6⟩ := hd
  have hf' : ∀ g c x, dict g = ⟨c, x⟩ → ∃ p : GA D V, ∀ τ : (X c).Ψ, mat x τ =
      Matrix.reindex (finCongr hr) (finCongr hr) (archM V (th c τ) p) * x₀ τ.1 := by
    intro g c x hg
    have := hf g
    rw [hg] at this
    exact this
  have h6' : ∀ g g' c x, dict g = ⟨c, x⟩ → (∃ γ' ∈ (X c).Γ, dict g' = ⟨c, lact γ' x⟩) →
      ∃ γ ∈ GQ V, ∃ k ∈ Kf, g' = γ * g * k := by
    intro g g' c x hg hh
    refine h6 g g' ?_
    rw [hg]
    exact hh
  obtain ⟨x', hx'⟩ : ∃ x' : Frame (X (dict h).1).Ψ r, dict h' = ⟨(dict h).1, x'⟩ := by
    generalize (dict h).1 = c at e
    subst e
    exact ⟨_, rfl⟩
  obtain ⟨hdom, g0, hg0⟩ := h0 (dict h).1
  obtain ⟨b, hb⟩ := hf' _ _ _ hg0
  obtain ⟨p, hp⟩ := hf h
  obtain ⟨p', hp'⟩ := hf' _ _ _ hx'
  obtain ⟨a, a1, a2⟩ := GlobalTheory.UnitarySplit.ga_glue V _ 1 (GlobalTheory.UnitarySplit.infHom_mem V (b * (p⁻¹ * p') * b⁻¹)) (one_mem _)
  obtain ⟨γ', hγ', he⟩ := h3 h a a2
  refine ⟨a, a2, h6' h' _ _ x' hx' ⟨γ', hγ', he.trans ?_⟩⟩
  congr 2
  funext τ
  have ha : archM V (th (dict h).1 τ) a = archM V (th (dict h).1 τ) (b * (p⁻¹ * p') * b⁻¹) := by
    unfold archM
    rw [a1]
  show (mat (dict h).2 τ * ((mat (x0 (dict h).1) τ)⁻¹ * Matrix.reindex (finCongr hr) (finCongr hr)
    (archM V (th (dict h).1 τ) a) * mat (x0 (dict h).1) τ) : Matrix (Fin r) (Fin r) ℂ) = mat x' τ
  have hy := (hdom τ).1
  rw [hb τ] at hy
  rw [hp τ, hp' τ, hb τ, ha]
  refine frame_calc _ _ _ (Matrix.reindex (finCongr hr) (finCongr hr) (archM V (th (dict h).1 τ) (p⁻¹ * p'))) _ _ hy ?_ ?_
  · rw [archM_mul, archM_mul, inv_mul_cancel_right]
  · rw [archM_mul, mul_inv_cancel_left]

theorem comm_real_fin (V : HSp D) {a k : GA D V} (ha : a ∈ GinfC V) (hk : k ∈ GfC V) : a * k = k * a := by
  refine GlobalTheory.UnitarySplit.ga_ext V ?_ ?_
  · rw [map_mul, map_mul, show infHom V k = 1 from hk, mul_one, one_mul]
  · rw [map_mul, map_mul, show finHom V a = 1 from ha, mul_one, one_mul]

theorem exists_action_dict {V W : HSp D} (hV : V = W) {X : Comp → Data E r} {dict : GA D V → Σ k, Frame (X k).Ψ r}
    {Kf : Subgroup (GA D V)} {th : ∀ c, (X c).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {hr : V.rank = r}
    (hd : DictIsUnif V dict Kf th hr) (x₀ : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (hf : ∀ h, ∃ p : GA D V, ∀ τ : (X (dict h).1).Ψ, mat (dict h).2 τ =
      Matrix.reindex (finCongr hr) (finCongr hr) (archM V (th (dict h).1 τ) p) * x₀ τ.1)
    (β : GL (Fin W.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ W.rank) {G : Type} [Group G] (eG : G →* G0 L.Pg L.r)
    (hK : ∀ k : GA D W, Lev.IsLevelLift W β L 1 k ↔ cast (congrArg (GA D) hV.symm) k ∈ Kf)
    (hex : ∀ g, ∃ k, Lev.IsLevelLift W β L (eG g) k) :
    ∃ mv : Comp → G → Comp, (∀ x, mv x 1 = x) ∧ (∀ x g g', mv x (g * g') = mv (mv x g) g') ∧
      (∀ x, ∃ h, (castDict hV dict h).1 = x) ∧ ∀ g k, Lev.IsLevelLift W β L (eG g) k →
        ∀ h, (castDict hV dict (h * k)).1 = mv (castDict hV dict h).1 g := by
  subst hV
  have hK' : ∀ k : GA D V, Lev.IsLevelLift V β L 1 k ↔ k ∈ Kf := hK
  refine exists_action (fun h => (dict h).1) (fun x => ?_) (fun g k => Lev.IsLevelLift V β L (eG g) k) hex ?_ ?_ ?_
  · obtain ⟨x0, h0, -⟩ := hd.2.2.1
    obtain ⟨g, hg⟩ := (h0 x).2
    exact ⟨g, congrArg Sigma.fst hg⟩
  · show Lev.IsLevelLift V β L (eG 1) 1
    rw [map_one]
    exact (hK' 1).2 (one_mem _)
  · intro g g' k k' hk hk'
    show Lev.IsLevelLift V β L (eG (g * g')) (k * k')
    rw [map_mul]
    exact GlobalTheory.ProjComm.isLift_mul hk hk'
  · intro g k k' h h' hk hk' e
    obtain ⟨a, ha, γ, hγ, k0, hk0, he⟩ := coset_of_comp_eq hd x₀ hf e
    have h1 := GlobalTheory.ProjComm.isLift_mul (GlobalTheory.ProjComm.isLift_mul (GlobalTheory.ProjComm.isLift_inv hk') ((hK' k0).2 hk0)) hk
    rw [mul_one, inv_mul_cancel] at h1
    have h2 : h * k * a = γ * (h' * k' * (k'⁻¹ * k0 * k)) := by
      rw [mul_assoc h, ← comm_real_fin V ha hk.1, ← mul_assoc h, he]
      group
    obtain ⟨x0, -, h3⟩ := hd.2.2.1
    obtain ⟨_, -, e1⟩ := h3 (h * k) a ha
    obtain ⟨_, -, e2⟩ := hd.1 γ hγ (h' * k' * (k'⁻¹ * k0 * k))
    obtain ⟨_, -, e3⟩ := hd.2.1 _ ((hK' _).1 h1) (h' * k')
    have f1 := congrArg Sigma.fst e1
    have f2 := congrArg Sigma.fst e2
    have f3 := congrArg Sigma.fst e3
    rw [h2] at f1
    exact f1.symm.trans (f2.trans f3)

set_option maxHeartbeats 1000000 in

theorem exists_action_components : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → TieIn T R κ v₀ → T.pb = R.C.P.pb → ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), GoodEmb T.Q.c σ → ∀ hV : T.V ((i : ℕ) + 1) σ = Wc D i, (∀ g, ∃ k, Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k) → ∃ mv : (T.U ((i : ℕ) + 1) σ).Comp → G → (T.U ((i : ℕ) + 1) σ).Comp, (∀ x, mv x 1 = x) ∧ (∀ x g g', mv x (g * g') = mv (mv x g) g') ∧ (∀ x, ∃ h, (castDict hV (T.dict ((i : ℕ) + 1) σ) h).1 = x) ∧ ∀ g k, Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k → ∀ h, (castDict hV (T.dict ((i : ℕ) + 1) σ) (h * k)).1 = mv (castDict hV (T.dict ((i : ℕ) + 1) σ) h).1 g := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ hR ht hpb i σ hσ hV hex
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  obtain ⟨th, hr, hth, hd⟩ := ht.laws.dictU _ hj σ hσ
  obtain ⟨hr', g, e, F, ik, φ, th', -, -, hth', -, hL⟩ := ht.laws.adPin _ hj σ hσ
  have e' : th' = th := funext fun k => funext fun τ => GlobalTheory.LettersCheck.isInfEmb_unique _ _ _ (hth' k τ) (hth k τ)
  subst e'
  exact exists_action_dict hV hd (T.x₀ _ σ) (fun h => (hL h).elim fun γ hγ => ⟨γ * h, hγ.2.2.2⟩)
    (R.βW i) (R.datWp i R.triv) R.eG.toMonoidHom (GlobalTheory.T.level_character_embedding_compat T R κ v₀ hR ht hpb i σ hσ hV) hex

end GlobalTheory.CompAct
