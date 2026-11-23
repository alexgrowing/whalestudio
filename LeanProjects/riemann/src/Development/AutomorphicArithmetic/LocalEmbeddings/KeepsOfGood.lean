import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.RootInCore
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankIInfKerSemilinear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeepsCuspLatticeNorm

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.CovTop.BadRep

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.BigTop GlobalTheory.AllWt GlobalTheory.CovTop GlobalTheory.BadCount
open GlobalTheory.LevDesc (TypeFrame IsTypeLevel typeRed typeEmb grpHR grpGHR transl levelGU)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters (Sq LevelGroup levelU psiU unitri superDiag)
open GlobalTheory.LevPull (CongMod)
open Formalism.MainNotions.ArithmeticCylinders
open scoped TensorProduct

section Group

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

set_option maxHeartbeats 1000000 in

theorem whit_data (R : RealDat D A Ks) (F : Face D A) (hlevels : R.grp_levels F) (c : G ≃* G0g D.nd)
    (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ R.Pg) (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1)
    (hpin : ∀ g kv, R.eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) (c g kv)) :
    ∃ (Pb : Subgroup (G0g D.nd)) (lam : Pb →* ℂˣ)
      (ψ : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), AddChar (ZMod (D.host.g kv.1)) ℂ), IsWhit D Pb lam ψ ∧
      (∀ g, c g ∈ Pb ↔ g ∈ (F.lvl false).P) ∧
      ∀ g (h : c g ∈ Pb) (h' : g ∈ (F.lvl false).P), ((lam ⟨c g, h⟩ : ℂˣ) : ℂ) =
        D.what₂.embLL (((F.lvl false).ψ⁻¹ ⟨g, h'⟩ : D.what₂.LLˣ) : D.what₂.LL) := by
  classical
  obtain ⟨ψ0, hgen, hlev, -⟩ := hlevels
  let P := (F.lvl false).P
  let Pb : Subgroup (G0g D.nd) := P.map c.toMonoidHom
  have hPb : ∀ g, g ∈ Pb ↔ c.symm g ∈ P := fun g => Subgroup.mem_map_equiv
  let toP : Pb →* P := (c.symm.toMonoidHom.comp Pb.subtype).codRestrict P fun x => (hPb x).1 x.2
  let lam : Pb →* ℂˣ := (Units.map (D.what₂.embLL : D.what₂.LL →* ℂ)).comp ((F.lvl false).ψ⁻¹.comp toP)
  let ψC : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), AddChar (ZMod (D.host.g kv.1)) ℂ := fun kv =>
    (ψ0 (plg kv).1).compAddMonoidHom ((iso kv).toAddMonoidHom.comp (-AddMonoidHom.id _))
  have hmemP : ∀ x : G, x ∈ P ↔ ∀ kv, c x kv ∈ unitri D.R.r (ZMod (D.host.g kv.1)) := by
    intro x
    have e1 : x ∈ P ↔ R.eG x ∈ (R.levR F false).H := by
      show _ ↔ R.eG.symm (R.eG x) ∈ P
      rw [MulEquiv.symm_apply_apply]
    rw [e1, hlev, GlobalTheory.TypeBase.mem_lastZeroOrthImageSubspace_iff, ← plg.forall_congr_right]
    refine forall_congr' fun kv => ?_
    rw [hpin, GlobalTheory.TypeBase.bc_mem_unip_iff]
  refine ⟨Pb, lam, ψC, ⟨fun kv h => hgen (plg kv).1 (plg kv).2 (AddChar.ext _ _ fun y => ?_), fun g => ?_, fun g => ?_⟩,
    fun g => by rw [hPb, MulEquiv.symm_apply_apply], fun g h h' => ?_⟩
  · obtain ⟨x, rfl⟩ := (iso kv).surjective y
    have := DFunLike.congr_fun h (-x)
    simpa [ψC] using this
  · rw [hPb, hmemP]
    refine forall_congr' fun kv => ?_
    rw [MulEquiv.apply_symm_apply, isUniUp_iff]
  · have hx : c.symm (g : G0g D.nd) ∈ P := (hPb _).1 g.2
    have hxH : R.eG (c.symm g) ∈ (R.levR F false).H := by
      show R.eG.symm (R.eG _) ∈ P
      rw [MulEquiv.symm_apply_apply]
      exact hx
    have e1 : (R.levR F false).chi ⟨_, hxH⟩ = Units.map (D.what₂.embLL : D.what₂.LL →* ℂ)
        ((F.lvl false).ψ ⟨R.eG.symm (R.eG (c.symm g)), hxH⟩) := rfl
    rw [show (⟨R.eG.symm (R.eG (c.symm g)), hxH⟩ : P) = ⟨c.symm g, hx⟩ from
      Subtype.ext (MulEquiv.symm_apply_apply _ _)] at e1
    have key : ∀ X : LevelP R.Pg D.R.r ℂ, X = P0 R.Pg D.R.r ψ0 → ∀ y (hy : y ∈ X.H),
        ((X.chi ⟨y, hy⟩ : ℂˣ) : ℂ) = ∏ PP : R.Pg, ψ0 PP.1 (edgeSum supEdge (y PP)) := by
      rintro X rfl y hy
      exact GlobalTheory.TypeBase.baseLevelCharacter_eq_prod_superdiagonalSum _ _ _ y hy
    have h3 := key _ hlev _ hxH
    rw [e1] at h3
    have ht : toP g = ⟨c.symm g, hx⟩ := rfl
    show ((Units.map (D.what₂.embLL : D.what₂.LL →* ℂ) ((F.lvl false).ψ⁻¹ (toP g)) : ℂˣ) : ℂ) = _
    rw [ht, MonoidHom.inv_apply, map_inv, Units.val_inv_eq_inv_val, h3, ← plg.prod_comp, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun kv _ => ?_
    rw [hpin, MulEquiv.apply_symm_apply, GlobalTheory.TypeBase.edgeSum_bc, sum_entN]
    show _ = ψ0 (plg kv).1 ((iso kv) (-(superDiag _)))
    rw [map_neg, AddChar.map_neg_eq_inv]
    rfl
  · have ht : toP ⟨c g, h⟩ = ⟨g, h'⟩ := Subtype.ext (c.symm_apply_apply g)
    show ((Units.map (D.what₂.embLL : D.what₂.LL →* ℂ) ((F.lvl false).ψ⁻¹ (toP ⟨c g, h⟩)) : ℂˣ) : ℂ) = _
    rw [ht]
    rfl

set_option maxHeartbeats 1000000 in

theorem half_data (R : RealDat D A Ks) (c : G ≃* G0g D.nd)
    (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ R.Pg) (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1)
    (hpin : ∀ g kv, R.eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) (c g kv))
    (ε : Sq D.host ≃ R.Pg) (iso' : ∀ v : Sq D.host, ZMod (D.host.g v.1) ≃+* kP (ε v).1) (t : LevelGroup D.host ≃* G)
    (t1 : ∀ u v, R.eG (t u) (ε v) = Formalism.UG.bc (iso' v : ZMod (D.host.g v.1) →+* kP (ε v).1) (u v)) (k : Fin 2) :
    ∃ H : Subgroup (G0g D.nd), IsHalf D k H ∧ ∀ u, c (t u) ∈ H ↔ u ∈ levelGU D.host k := by
  refine ⟨Subgroup.pi {kv | kv.1 ≠ k} fun kv => unitri D.R.r (ZMod (D.host.g kv.1)),
    fun g => forall_congr' fun kv => imp_congr_right fun _ => (isUniUp_iff _).symm, fun u => ?_⟩
  refine ((ε.trans plg.symm).forall_congr fun v => ?_).symm
  have he : plg ((ε.trans plg.symm) v) = ε v := plg.apply_symm_apply _
  generalize (ε.trans plg.symm) v = kv at he
  have hk : v.1 = kv.1 := idx_eq (iso' v) (iso kv) (by rw [he])
  show (v.1 ≠ k → _) ↔ (kv.1 ≠ k → _)
  rw [hk]
  refine imp_congr_right fun _ => ?_
  show u v ∈ unitri D.R.r (ZMod (D.host.g v.1)) ↔ c (t u) kv ∈ unitri D.R.r (ZMod (D.host.g kv.1))
  rw [← GlobalTheory.TypeBase.bc_mem_unip_iff (iso' v), ← GlobalTheory.TypeBase.bc_mem_unip_iff (iso kv), ← hpin, ← t1, he]

end Group

section Point

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

set_option maxHeartbeats 1000000 in

theorem keeps_of_good {T : CoreJ D} (hJ : LawsJ T) {j : ℕ} (hpq : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q) (Y : Deep T.toCore j) {e : ℕ}
    {o : ℝ} (hY : Y.Good e o) {G : WTZ D.host.E} (hG : Even G.2) : GlobalTheory.LevDesc.KeepsCusp Y.U G := by
  have hA := hY.lev.2
  have hM : Y.d.l₂.M = D.host.g 0 * D.host.g 1 * Y.d.pd := by rw [hY.lev.1.2.1, hJ.pins.2.1.1]
  have hχ := fun σ hσ => GlobalTheory.AllWt.Model.chi_modelWt (Y.U σ) (hY.chiTriv σ hσ) G hG
  obtain ⟨ι, hι, -, hpin⟩ := hY.adPin
  refine GlobalTheory.LevelKeeps.keepsCusp_of_isUnf hpq hA hG hY.unf (fun σ hσ k k' => ?_) (fun σ hσ => ?_) hχ
  · obtain ⟨hr, hW⟩ := hY.modelW σ hσ
    exact ⟨(hW k).1.trans (hW k').1.symm, (hW k).2.trans (hW k').2.symm⟩
  · obtain ⟨hr, hW⟩ := hY.modelW σ hσ
    obtain ⟨th, _, hth, hD⟩ := hY.dictU σ hσ
    obtain ⟨x₀, h0, _, g, e, F, ik, φ, th', hth', hL⟩ := hpin σ hσ
    obtain rfl : th = th' := funext fun k => funext fun τ =>
      GlobalTheory.LettersCheck.isInfEmb_unique τ.1 _ _ (hth k τ) (hth' k τ)
    exact GlobalTheory.LevelKeeps.mem_group (hY.unf σ hσ) hA ((hY.unf σ hσ).1 ▸ hpq) hr hW h0 (hM ▸ hY.levelK) hth hD fun h => by
      obtain ⟨γ, -, -, -, h3⟩ := hL.2 h
      exact ⟨_, h3⟩

theorem basis_of_form {K M R V : Type} [Field K] [Field M] [Algebra K M] [AddCommGroup R] [Module K R] [AddCommGroup V]
    [Module K V] [Module M V] {C C' : Submodule K R} (hC : C' = C) {W : Submodule K V} (e : C ≃ₗ[K] W) {n : ℕ} (b : Fin n → V)
    (h1 : ∀ k, b k ∈ W) (h2 : LinearIndependent K b) (h3 : Submodule.span K (Set.range b) = W) :
    ∃ (ε : C' →ₗ[K] V) (b' : Fin n → C'), (∀ (f : C') (h : (f : R) ∈ C), ε f = e ⟨f, h⟩) ∧ (∀ k, ε (b' k) = b k) ∧
      LinearIndependent K b' ∧ Submodule.span K (Set.range b') = ⊤ := by
  subst hC
  have hb : ∀ k, (W.subtype ∘ₗ e.toLinearMap) (e.symm ⟨b k, h1 k⟩) = b k := fun k => by simp
  refine ⟨W.subtype ∘ₗ e.toLinearMap, fun k => e.symm ⟨b k, h1 k⟩, fun f h => rfl, hb, ?_, ?_⟩
  · exact LinearIndependent.of_comp (W.subtype ∘ₗ e.toLinearMap) (by convert h2 using 1; exact funext hb)
  · refine Submodule.map_injective_of_injective (f := W.subtype ∘ₗ e.toLinearMap)
      (W.injective_subtype.comp e.injective) ?_
    rw [Submodule.map_span, ← Set.range_comp, show (W.subtype ∘ₗ e.toLinearMap) ∘ (fun k => e.symm ⟨b k, h1 k⟩) = b from funext hb,
      h3, Submodule.map_top, LinearMap.range_comp, LinearEquiv.range, Submodule.map_top, Submodule.range_subtype]

set_option maxHeartbeats 1000000 in

theorem rank_gen {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F}
    {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
    (fw : FWTie T R κ v₀) (Fc : Face D A) (i : Fin D.R.m) (act : G → T.R ((i : ℕ) + 1) →ₗ[T.Q.c.F] T.R ((i : ℕ) + 1))
    (hρ : ActRho R i (T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n) (fw.e i) act)
    {C : Submodule T.Q.c.F (T.R ((i : ℕ) + 1))} (hC : C = T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n)
    {F V Γ G' : Type} [Field F] [Algebra F ℂ] [AddCommGroup V] [Module F V] [Group Γ] [Finite Γ] [Group G']
    {j : T.Q.c.F →+* F} (hj : ∀ a, algebraMap F ℂ (j a) = T.σ₀ a) (π : C →ₛₗ[j] V) (τ : Representation F Γ V) (θ : Γ →* G)
    (q1 : ∀ (m : ℕ) (b : Fin m → C), LinearIndependent T.Q.c.F b → LinearIndependent F fun k => π (b k))
    (q2 : ∀ γ (v : C), ∃ hv : act (θ γ) v ∈ C, τ γ (π v) = π ⟨_, hv⟩)
    (q3 : ∀ v, (∀ γ, θ γ = 1 → τ γ v = v) → v ∈ Submodule.span F (Set.range π))
    (c : G ≃* G') (s : G' →* Γ) (hs : ∀ g, θ (s (c g)) = g) (Q : Subgroup Γ)
    (hQ : ∀ γ, γ ∈ Q ↔ θ γ ∈ (Fc.lvl false).P) (lamb : Q →* ℂˣ)
    (hlam : ∀ γ : Q, ((lamb γ : ℂˣ) : ℂ) =
      D.what₂.embLL (((Fc.lvl false).ψ⁻¹ ⟨θ γ, (hQ _).1 γ.2⟩ : D.what₂.LLˣ) : D.what₂.LL))
    (e0 : MonoidAlgebra ℂ G') (he : ∀ g, D.what₂.embLL ((idemOf A.X).coeff g) = e0.coeff (c g)) :
    ∃ (ρ : Representation ℂ Γ (ℂ ⊗[F] V)) (χ : Γ →* ℂˣ),
      (∀ (g : Γ) (v : V), ρ g ((1 : ℂ) ⊗ₜ[F] v) = ((χ g : ℂˣ) : ℂ) • ((1 : ℂ) ⊗ₜ[F] τ g v)) ∧
      Formalism.HN.rkK (latType R Fc i) = Module.finrank ℂ (eig ρ Q lamb) ∧
      Formalism.HN.rkK (CovTop.latBad R Fc i) = Module.finrank ℂ (eig ρ Q lamb ⊓
        LinearMap.ker (Representation.asAlgebraHom (ρ.comp s : Representation ℂ G' (ℂ ⊗[F] V)) e0) :
          Submodule ℂ (ℂ ⊗[F] V)) := by
  obtain ⟨n, b, b1, b2, b3, b4, b5⟩ := fw.ks i
  obtain ⟨ε, b', e1, e2, e3, e4⟩ := basis_of_form (M := D.what₂.LL) hC (fw.e i) b b1 b2 b3
  have H := GlobalTheory.BadCount.RankRead.finrank_eq (M := ℂ) D.what₂.embLL
    (fun a => (RingHom.congr_fun (res_embLL T fw.alg_eq fw.laws.pins.2.2.1) a).trans (hj a).symm) ε π b' e4
    (by simpa only [e2] using b4) (by simpa only [e2] using b5) (q1 n b' e3)
    (R.FW i).ρ (R.FW i).chi τ θ c s hs
    (fun γ f => by
      obtain ⟨hv, h⟩ := q2 γ f
      have hf : (f : T.R ((i : ℕ) + 1)) ∈ T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n := hC ▸ f.2
      obtain ⟨hf', h'⟩ := hρ (θ γ) ⟨f, hf⟩
      exact ⟨⟨_, hv⟩, by rw [e1 f hf, e1 ⟨_, hv⟩ hf']; exact h'.symm, h⟩)
    q3 (Fc.lvl false).P (Fc.lvl false).ψ⁻¹ Q hQ lamb hlam (spType R Fc i) (fun _ => Iff.rfl)
    (fun g => (idemOf A.X).coeff g) e0 he
  have hM := GlobalTheory.GoodLat.Obj.mkFull_of_tie fw i
  refine ⟨_, _, fun g v => GlobalTheory.BadCount.RankRead.twistExt_tmul _ _ _ _ _,
    (GlobalTheory.BadCount.RankRead.rkK_inf _ (fw.ks i) hM _).trans H.1, Eq.trans ?_ H.2⟩
  rw [← GlobalTheory.BadCount.RankRead.rkK_inf _ (fw.ks i) hM, Submodule.restrictScalars_inf, ← inf_assoc]
  rfl

set_option maxHeartbeats 1000000 in

theorem rep_data {T : CoreJ D} (hT : LawsJ T) {j : ℕ} (hj : InR D j) (Y : Deep T.toCore j) {e : ℕ} {o : ℝ} (hY : Y.Good e o)
    {a : (D.host.E →+* ℂ) × ℕ → ℕ} {n : ℕ} (hD : Dom a n) {G : Type} [Group G]
    (lev : G → (T.Q.Dw j).La →ₗ[𝓞 D.host.E] (T.Q.Dw j).La)
    (hact : ActLev (Xo := T.Q.Xo j) T.Q.c (fun g => (lev g, (LinearMap.id : (T.Q.Dw j).La →ₗ[𝓞 D.host.E] (T.Q.Dw j).La))))
    (hk : ∀ g, ∀ f ∈ T.cuspA j a n, actLev (Xo := T.Q.Xo j) T.Q.c
      (fun g => (lev g, (LinearMap.id : (T.Q.Dw j).La →ₗ[𝓞 D.host.E] (T.Q.Dw j).La))) g f ∈ T.cuspA j a n)
    (θ : LevelAut (T.Q.Dw j) Y.d.l₂ →* G) (h1 : ∀ γ, CongMod T.Q.l.Mb (liftLa γ) (lev (θ γ)))
    (h2 : ∀ γ, CongMod T.Q.l.Mb (liftLa γ) LinearMap.id → θ γ = 1) :
    ∃ (π : cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n) →ₛₗ[((Y.d.eF : Y.c'.F →+* Y.d.c₂.F).comp (incF T.Q.c Y.c' Y.hle))]
        Y.V (wtZ a n)) (τ : Representation Y.d.c₂.F (LevelAut (T.Q.Dw j) Y.d.l₂) (Y.V (wtZ a n))),
      (∀ g v, (τ g v : Rul Y.d.Xo₂ Y.d.c₂) = transl Y.d.Xo₂ Y.d.c₂ g v) ∧
      (∀ (m : ℕ) (b : Fin m → cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n)), LinearIndependent T.Q.c.F b →
        LinearIndependent Y.d.c₂.F fun k => π (b k)) ∧
      (∀ γ (v : cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n)), ∃ hv : actLev (Xo := T.Q.Xo j) T.Q.c
        (fun g => (lev g, (LinearMap.id : (T.Q.Dw j).La →ₗ[𝓞 D.host.E] (T.Q.Dw j).La))) (θ γ) v ∈
          cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n), τ γ (π v) = π ⟨_, hv⟩) ∧
      (∀ v, (∀ γ, θ γ = 1 → τ γ v = v) → v ∈ Submodule.span Y.d.c₂.F (Set.range π)) := by
  have hpq : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by
    obtain ⟨hp, hq, -⟩ := (GlobalTheory.LevGeo.laws_of_coreJ D T j hT hj).1.dat
    obtain ⟨h1, h2⟩ := hj
    have hk := D.R.m_add_three_le_k
    rw [hp, hq]
    simp only [Ranks.sigW]
    omega
  have hA' : Y.d.l₂.A.Coprime Y.d.l₂.M := by rw [hY.lev.2]; exact Nat.coprime_one_left _
  have hKC : GlobalTheory.LevDesc.KeepsCusp Y.U (wtZ a n) := keeps_of_good hT hpq Y hY ((Int.even_coe_nat _).2 hD.2)
  obtain ⟨π, q1, q2, q3⟩ := pull_data D T j Y e o hT hj hY a n hD G lev hact hk θ h1
  have hτ := GlobalTheory.LevDesc.coe_cuspRep Y.U (wtZ a n) hpq hA' hKC
  exact ⟨π, _, hτ, q1, fun γ v => (q2 γ v).imp fun hv h => Subtype.ext ((hτ γ _).trans h),
    fun v hv => q3 v fun γ hγ => (hτ γ v).symm.trans (congrArg Subtype.val (hv γ (h2 γ hγ)))⟩

end Point

end GlobalTheory.CovTop.BadRep
