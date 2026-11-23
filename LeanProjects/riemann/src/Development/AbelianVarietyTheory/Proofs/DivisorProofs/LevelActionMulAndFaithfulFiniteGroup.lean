import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransp
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MulVecMemOfFrame
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinCongMemLevEnv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaFormNonvanishing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CongruenceOnSelfDualLatticeOfDatumImageStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CongruenceOnSelfDualLatticeCompletionStatement
open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn

set_option autoImplicit false
noncomputable section
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped Matrix TensorProduct Pointwise

namespace GlobalTheory.LevelFaithful

theorem bc_eq_one_of_cong {R : Type} [CommRing R] {n : ℕ} (S : Subring R) (β : GL (Fin n) R) (H : Set (Fin n → R)) (N : ℕ)
    (hH : ∀ z, z ∈ H ↔ ∀ i, ((β⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R).mulVec z i ∈ S)
    (y : GL (Fin n) S) (s : S)
    (hx : ∀ z ∈ H, ∃ w ∈ H, (s : R) • ((β * Formalism.UG.bc S.subtype y * β⁻¹ : GL (Fin n) R).1 *ᵥ z - z) = N • w)
    {k : Type} [CommRing k] (φ : S →+* k) (hN : (N : k) = 0) (hs : IsUnit (φ s)) : Formalism.UG.bc φ y = 1 := by
  have key : ∀ i j, φ (y.1 i j) = (1 : Matrix (Fin n) (Fin n) k) i j := by
    intro i j
    have e0 : (β⁻¹).1 *ᵥ (β.1 *ᵥ Pi.single j 1) = Pi.single j 1 := by
      rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    obtain ⟨w, hw, e⟩ := hx (β.1 *ᵥ Pi.single j 1) ((hH _).2 fun i => by
      rw [e0, Pi.single_apply]; split_ifs; exacts [one_mem _, zero_mem _])
    have e1 := congrArg (fun v => ((β⁻¹).1 *ᵥ v) i) e
    have hy : (Formalism.UG.bc S.subtype y).1 i j = (y.1 i j : R) := rfl
    simp only [Matrix.mulVec_smul, Matrix.mulVec_sub, e0, Units.val_mul, Matrix.mulVec_mulVec, ← Matrix.mul_assoc,
      Units.inv_mul, Matrix.one_mul] at e1
    rw [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one, Matrix.mulVec_single_one] at e1
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Matrix.col_apply, hy] at e1
    have hc := (hH w).1 hw i
    have e2 : s * (y.1 i j - (Pi.single j 1 : Fin n → S) i) = N • (⟨_, hc⟩ : S) := by
      apply Subtype.ext
      change (s : R) * ((y.1 i j : R) - ((Pi.single j (1 : S) : Fin n → S) i : R)) =
        N • (((β⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) *ᵥ w) i
      rw [← e1]
      congr 2
      rw [Pi.single_apply, Pi.single_apply]
      split_ifs <;> simp
    have e3 := congrArg φ e2
    rw [map_mul, map_nsmul, nsmul_eq_mul, hN, zero_mul, hs.mul_right_eq_zero, map_sub, sub_eq_zero] at e3
    rw [e3, Pi.single_apply, Matrix.one_apply]
    split_ifs <;> simp
  refine Units.ext (Matrix.ext fun i j => ?_)
  exact key i j

theorem cong_swap_smul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (Λ : Submodule (𝓞 E) (Fin n → E)) (N : ℕ) (t : FiniteAdeleRing (𝓞 F) F ⊗[F] E)
    (K : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F ⊗[F] E))
    (h : ∀ z ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E)), ∃ y ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E)),
      t • (K *ᵥ z - z) = N • y) :
    ∀ z ∈ Formalism.L2.Herm.hatL (F := F) Λ, ∃ y ∈ Formalism.L2.Herm.hatL (F := F) Λ,
      Algebra.TensorProduct.comm F _ E t • (K.map (Algebra.TensorProduct.comm F _ E) *ᵥ z - z) = N • y := by
  intro z hz
  obtain ⟨y, hy, e⟩ := h _ (GlobalTheory.PrincInLevel.swap_symm_mem_hat Λ z hz)
  refine ⟨_, GlobalTheory.PrincInLevel.swap_mem_hatL Λ y hy, funext fun i => ?_⟩
  have := congrArg (Algebra.TensorProduct.comm F _ E) (congrFun e i)
  simpa only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_mul, map_nsmul, Matrix.mulVec, dotProduct, map_sum,
    AlgEquiv.apply_symm_apply, Matrix.map_apply] using this

end GlobalTheory.LevelFaithful

namespace GlobalTheory.LevelFaithful

variable {D : D7}

theorem smul_mem_latGHat {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hβ : IsSDFrame V β Λ 1) (c : 𝓞 D.host.E) {w : Fin V.rank → FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E}
    (hw : w ∈ latGHat V 1) :
    ((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] ((c : 𝓞 D.host.E) : D.host.E)) • w ∈ latGHat V 1 := by
  have hl' : latHat V = GlobalTheory.AdLat.hat D.host.F ((Λ : Submodule (𝓞 D.host.E) _) : Set (Fin V.rank → D.host.E)) :=
    (GlobalTheory.OneMapRef.Lift.hatV_eq hβ).symm
  set s : FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E :=
    (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] ((c : 𝓞 D.host.E) : D.host.E) with hs
  have e : ∀ z : Fin V.rank → FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E,
      Matrix.diagonal (fun _ => s) *ᵥ z = s • z := fun z => by
    funext j; rw [Matrix.mulVec_diagonal]; rfl
  have hN : ∀ z ∈ latHat V, Matrix.diagonal (fun _ => s) *ᵥ z ∈ latHat V := by
    intro z hz
    rw [e]
    rw [hl'] at hz ⊢
    have := GlobalTheory.PrincInLevel.smul_mem_hat Λ _ (Formalism.L2.DIV.oToS D.host.F D.host.E c).2 z hz
    convert this using 2
    rw [Formalism.L2.DIV.oToS_coe, Algebra.TensorProduct.comm_symm_tmul]
  rw [← e]
  exact GlobalTheory.LevelUnique.mulVec_mem_latGHat _ hN w hw

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem cong_of_trivial {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hβ : IsSDFrame V β Λ 1) {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La]
    {ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)} (hι : LatEmb V ι) {M : ℕ} {Mb Mh : Ideal (𝓞 D.host.E)}
    (hprod : Mb * Mh = Ideal.span {(M : 𝓞 D.host.E)}) {c : 𝓞 D.host.E} (hc : c ∈ Mh) {f : La →ₗ[𝓞 D.host.E] La}
    (hd : ∀ a, f a - a ∈ Mb • (⊤ : Submodule (𝓞 D.host.E) La))
    (K : Matrix (Fin V.rank) (Fin V.rank) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E))
    (hcong : ∀ a ∈ Mh • (⊤ : Submodule (𝓞 D.host.E) La), ∃ w ∈ latGHat V 1,
      finVec V (ι (f a)) - K *ᵥ finVec V (ι a) = M • w) (a : La) :
    ∃ w ∈ latGHat V 1,
      (((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] ((c : 𝓞 D.host.E) : D.host.E)) *
        ((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] ((c : 𝓞 D.host.E) : D.host.E))) •
        (K *ᵥ finVec V (ι a) - finVec V (ι a)) = M • w := by
  set s : FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E :=
    (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] ((c : 𝓞 D.host.E) : D.host.E) with hs
  obtain ⟨w, hw, e⟩ := hcong (c • a) (Submodule.smul_mem_smul hc Submodule.mem_top)
  have hdm : c • (f (c • a) - c • a) ∈ (M : 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) La) := by
    have := Submodule.smul_mem_smul hc (hd (c • a))
    rw [← Submodule.mul_smul, mul_comm, hprod, Submodule.ideal_span_singleton_smul] at this
    exact this
  obtain ⟨m, -, hm'⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hdm
  set F := GlobalTheory.LevelActionPinned.fvec V ι with hF
  have eF : ∀ (b : 𝓞 D.host.E) x, F (b • x) =
      ((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] (b : D.host.E)) • F x :=
    fun b x => GlobalTheory.LevelActionPinned.fvec_smul V ι b x
  have E1 : F (c • a) = s • F a := eF c a
  have eM : ((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] (((M : ℕ) : 𝓞 D.host.E) : D.host.E)) =
      ((M : ℕ) : FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E) := by
    have h0 : (((M : ℕ) : 𝓞 D.host.E) : D.host.E) = ((M : ℕ) : D.host.E) := by simp
    rw [h0]
    exact map_natCast (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] _) _
  have E2 : s • (F (f (c • a)) - F (c • a)) = M • F m := by
    rw [← map_sub, ← eF, ← hm', eF, eM, Nat.cast_smul_eq_nsmul]
  have e' : F (f (c • a)) - K *ᵥ F (c • a) = M • w := e
  refine ⟨F m - s • w, sub_mem (((GlobalTheory.MarkCoset.latG_spec D V 1).1 _).1
    (hι.2 ▸ LinearMap.mem_range_self ι m)) (smul_mem_latGHat hβ c hw), ?_⟩
  show (s * s) • (K *ᵥ F a - F a) = _
  calc (s * s) • (K *ᵥ F a - F a) = s • (K *ᵥ (s • F a) - s • F a) := by
        rw [mul_smul, Matrix.mulVec_smul K s (F a), smul_sub]
    _ = s • ((F (f (c • a)) - F (c • a)) - M • w) := by
        rw [← E1, ← e']; congr 1; abel
    _ = M • (F m - s • w) := by
        rw [smul_sub, E2, smul_comm s M w, smul_sub]

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem rTup_eq_one_of_cong {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hβ : IsSDFrame V β Λ 1) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) {M : ℕ} {c : 𝓞 D.host.E}
    (hM : ∀ PP ∈ L.Pg, ((M : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) (hc : ∀ PP ∈ L.Pg, c - 1 ∈ PP.asIdeal) {κ : GA D V}
    (hκ : Lev.finE V κ ∈ Formalism.L2.DIV.St β)
    (h : ∀ z ∈ latHat V, ∃ y ∈ latHat V,
      (((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] ((c : 𝓞 D.host.E) : D.host.E)) *
        ((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] ((c : 𝓞 D.host.E) : D.host.E))) •
        ((finHom V κ).1 *ᵥ z - z) = M • y) :
    Formalism.L2.DIV.rTup β L (Lev.finE V κ) = 1 := by
  have hl' : latHat V = GlobalTheory.AdLat.hat D.host.F ((Λ : Submodule (𝓞 D.host.E) _) : Set (Fin V.rank → D.host.E)) :=
    (GlobalTheory.OneMapRef.Lift.hatV_eq hβ).symm
  rw [hl'] at h
  have hS := cong_swap_smul Λ M _ _ h
  obtain ⟨yi, hyi⟩ := hκ
  obtain ⟨cc, hfr, -⟩ := hβ
  have hx : ∀ z ∈ (Formalism.L2.Herm.hatL (F := D.host.F) Λ : Set (Fin V.rank → Lev.EAf D)), ∃ w ∈
      (Formalism.L2.Herm.hatL (F := D.host.F) Λ : Set (Fin V.rank → Lev.EAf D)),
      ((Formalism.L2.DIV.oToS D.host.F D.host.E (c * c) : Formalism.L2.Herm.intAf D.host.F D.host.E) : Lev.EAf D) •
        ((β * Formalism.UG.bc (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype yi * β⁻¹ : GL (Fin V.rank) (Lev.EAf D)).1 *ᵥ z - z) =
        M • w := by
    intro z hz
    obtain ⟨y, hy, e⟩ := hS z hz
    refine ⟨y, hy, ?_⟩
    have hs' : ((Formalism.L2.DIV.oToS D.host.F D.host.E (c * c) : Formalism.L2.Herm.intAf D.host.F D.host.E) : Lev.EAf D) =
        Algebra.TensorProduct.comm D.host.F (FiniteAdeleRing (𝓞 D.host.F) D.host.F) D.host.E
          (((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] ((c : 𝓞 D.host.E) : D.host.E)) *
            ((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] ((c : 𝓞 D.host.E) : D.host.E))) := by
      rw [Formalism.L2.DIV.oToS_coe, Algebra.TensorProduct.tmul_mul_tmul, one_mul, Algebra.TensorProduct.comm_tmul, map_mul]
    have e2 : β * Formalism.UG.bc (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype yi * β⁻¹ = Formalism.L2.DIV.frGL β yi := rfl
    have hK' : (β * Formalism.UG.bc (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype yi * β⁻¹ : GL (Fin V.rank) (Lev.EAf D)).1 =
        (finHom V κ).1.map (Algebra.TensorProduct.comm D.host.F (FiniteAdeleRing (𝓞 D.host.F) D.host.F) D.host.E) := by
      rw [e2, hyi]
      rfl
    rw [hs', hK']
    exact e
  have hred : ∀ PP ∈ L.Pg, Formalism.L2.DIV.redFn β PP (Lev.finE V κ) = 1 := by
    intro PP hP
    have hN : ((M : ℕ) : Formalism.L2.DIV.kP PP) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk PP.asIdeal)]
      exact Ideal.Quotient.eq_zero_iff_mem.2 (hM PP hP)
    have hsu : IsUnit (Formalism.L2.DIV.resS D.host.F PP (Formalism.L2.DIV.oToS D.host.F D.host.E (c * c))) := by
      rw [Formalism.L2.DIV.resS_oToS]
      have e1 : Ideal.Quotient.mk PP.asIdeal c = 1 := by
        rw [← map_one (Ideal.Quotient.mk PP.asIdeal)]
        exact Ideal.Quotient.eq.2 (hc PP hP)
      rw [map_mul, e1, mul_one]
      exact isUnit_one
    have hr := bc_eq_one_of_cong (Formalism.L2.Herm.intAf D.host.F D.host.E) β
      (Formalism.L2.Herm.hatL (F := D.host.F) Λ : Set (Fin V.rank → Lev.EAf D)) M hfr yi
      (Formalism.L2.DIV.oToS D.host.F D.host.E (c * c)) hx (Formalism.L2.DIV.resS D.host.F PP) hN hsu
    rw [← hyi, Formalism.L2.DIV.redFn_frGL, hr]
  have e3 : Formalism.L2.DIV.rTup β L (Lev.finE V κ) = Formalism.L2.DIV.rTup β L 1 := by
    funext PP
    show Formalism.L2.DIV.upperLeftBlock _ _ = Formalism.L2.DIV.upperLeftBlock _ _
    rw [hred PP.1 PP.2, Formalism.L2.DIV.redFn_one]
  rw [e3, Formalism.L2.DIV.rTup_one]

end GlobalTheory.LevelFaithful

open GlobalTheory.LevelFaithful in
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem GlobalTheory.LevelFaithful.lev_mul_and_faithful : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), More p → ∀ (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r), OwnPin r → ∀ (i : Fin D.R.m), (∀ g g' : p.P.Gp, r.lev i (g * g') = r.lev i g * r.lev i g') ∧ ∀ g : p.P.Gp, r.lev i g = 1 → g = 1 := by
  intro D L hT Gi Gl Kc Y cX ex Csz p _ r h _ i
  obtain ⟨v⟩ := GlobalTheory.ShareOn.nonempty_place D
  have hlev := h.level v i
  have hι := GlobalTheory.TraceLattice.latEmb_iotaW (h.laws v) i
  have hβ : IsSDFrame (Wc D i) ((R2 p).βW i) ((R2 p).ΛW i) 1 := p.charW.base.lev.βW i
  obtain ⟨h1, hm⟩ := GlobalTheory.LevelActionPinned.congr_of_levIs (R2 p) i hι hβ h.half hlev
  refine ⟨fun g g' => ?_, fun g hg => ?_⟩
  · refine LinearEquiv.ext fun x => ?_
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have e1 := liftLa_spec (r.lev i (g * g')) a
    have e2 := liftLa_spec (r.lev i g) (liftLa (r.lev i g') a)
    have e3 := liftLa_spec (r.lev i g') a
    simp only [Submodule.mkQ_apply] at e1 e2 e3
    rw [LinearEquiv.mul_apply, ← e3, ← e2, ← e1]
    exact (Submodule.Quotient.eq _).2 (hm g g' a)
  · apply (R2 p).eG.injective
    rw [map_one]
    obtain ⟨κ, hκ, hcong⟩ := hlev g
    rw [← hκ.2.2]
    have hd : ∀ a, liftLa (r.lev i g) a - a ∈
        p.T.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (p.T.Q.Dw ((i : ℕ) + 1)).La) := by
      intro a
      rw [hg, ← Submodule.Quotient.eq]
      exact liftLa_spec 1 a
    obtain ⟨b, hb, c, hc, hbc⟩ := Submodule.mem_sup.1
      (p.T.Q.l.coprime ▸ Submodule.mem_top : (1 : 𝓞 D.host.E) ∈ p.T.Q.l.Mb ⊔ Mfr p.T.Q.l)
    have hc1 : c - 1 ∈ p.T.Q.l.Mb := by
      have e : c - 1 = -b := by rw [← hbc]; ring
      rw [e]; exact neg_mem hb
    have hMbP : ∀ PP ∈ (R2 p).Pg, p.T.Q.l.Mb ≤ PP.asIdeal := fun PP hP => by
      rw [h.half]; exact Ideal.prod_le_inf.trans (Finset.inf_le hP)
    have hp : p.T.Q.l.Mb * Mfr p.T.Q.l = Ideal.span {((p.T.Q.l.M : ℕ) : 𝓞 D.host.E)} := p.T.Q.l.prod
    have hMm : ((p.T.Q.l.M : ℕ) : 𝓞 D.host.E) ∈ p.T.Q.l.Mb := by
      have h0 : ((p.T.Q.l.M : ℕ) : 𝓞 D.host.E) ∈ p.T.Q.l.Mb * Mfr p.T.Q.l := by
        rw [hp]; exact Ideal.mem_span_singleton_self _
      exact (Ideal.mul_le_inf.trans (inf_le_left : p.T.Q.l.Mb ⊓ Mfr p.T.Q.l ≤ p.T.Q.l.Mb)) h0
    have hA := cong_of_trivial hβ hι hp hc hd _ hcong
    have hB := GlobalTheory.T.congruence_on_selfDual_lattice_completion (Wc D i) hβ _ _ _ (GlobalTheory.T.congruence_on_selfDual_lattice_of_datum_image (Wc D i) hβ hι _ _ _ hA)
    exact rTup_eq_one_of_cong hβ ((R2 p).datWp i (R2 p).triv) (fun PP hP => hMbP PP hP hMm)
      (fun PP hP => hMbP PP hP hc1) (Formalism.L2.DIV.parLev_St hκ.2.1) hB
