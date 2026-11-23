import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.KerSideCut
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.STiesR
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.SpOfRwRange
import Formalism.LocalToGlobal.IndefiniteReal.TrISepWith

noncomputable section

open scoped InnerProductSpace
open MeasureTheory Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.RowDict Formalism.L2.SG.ColDict Formalism.L2.SG.KerJoinS Formalism.L2.SG.KerSideCut Formalism.IndefR.Cx Formalism.L2.Indef

set_option linter.dupNamespace false

namespace Formalism.L2.SG.JoinSI

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Twist

variable {D : D7} (X : HidaSetting D) (G : GoodOp X) (j : D.what₂.EE ≃ₗᵢ[ℂ] EEC X G)
  {Fm : ∀ u, Formalism.L2.Forms.Forms0 D u} (Tr : ∀ u, Transport X u (Fm u)) (hK : X.LevelSubgroupCharacter)
  (Dt : D.what₂.Word → Set X.B.I.GA)
  {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs}
  (P : CxData A) {fc : DefSub A → DefFace Bs}
  (eV : ∀ t, (Fin ((fc P.zs).Df1.nV t) → K) →ₗ[K] A.FR t) (sEE : P.EE →ₗ⋆[ℂ] (fc P.zs).Sp.HH)
  (s : Bool) (σ : K →+* ℂ)
  (m : D.what₂.Word → (fc P.zs).Dc.Mem)
  (cφ : ∀ u, D.what₂.Mu u ≃ₗ[ℂ] (Fin ((fc P.zs).Dc.a (m u)) → ℂ))
  (cF : (Fin ((fc P.zs).Df1.nV Bs.μ0) → ℂ) →ₗ[ℂ] D.what₂.Amb D.what₂.mu0)
  (eR : D.what₂.EE →ₛₗ[Formalism.IndefR.Links.cj s] P.EE)

def cjv {n : ℕ} (x : Fin n → ℂ) : Fin n → ℂ := fun i => Formalism.IndefR.Links.cj s (x i)

theorem cjv_cjv {n : ℕ} (x : Fin n → ℂ) : cjv s (cjv s x) = x := by
  funext i
  cases s <;> simp [cjv, Formalism.IndefR.Links.cj]

theorem cjv_add {n : ℕ} (x y : Fin n → ℂ) : cjv s (x + y) = cjv s x + cjv s y := by
  funext i
  simp [cjv]

theorem cjv_smul {n : ℕ} (r : ℂ) (x : Fin n → ℂ) : cjv s (r • x) = Formalism.IndefR.Links.cj s r • cjv s x := by
  funext i
  simp [cjv]

theorem cjv_single {n : ℕ} (i : Fin n) : cjv s (Pi.single i (1 : ℂ)) = Pi.single i 1 := by
  funext k
  unfold cjv
  by_cases h : k = i <;> simp [h, Pi.single_apply]

def ChainTieT : Prop :=
  ∀ u (x : Fin ((fc P.zs).Dc.a (m u)) → K) (y : Fin ((fc P.zs).Df1.nV Bs.μ0) → K),
    D.what₂.perCol u D.what₂.mu0 ((cφ u).symm (cpt σ x)) (cF (cpt σ y)) = σ ((fc P.zs).Dc.Pt (m u) Bs.μ0 x y)

def RowTieT : Prop :=
  (∀ F, eR F ∈ P.EEl true) ∧ (∀ e ∈ P.EEl true, ∃ F, eR F = e) ∧ (∃ c : ℝ, 0 < c ∧ ∀ F, ‖eR F‖ = c * ‖F‖) ∧
    ∃ lam : ℂ, lam ≠ 0 ∧ ∀ y : Fin ((fc P.zs).Df1.nV Bs.μ0) → K,
      P.Θ Bs.μ0 (P.jR Bs.μ0 (eV Bs.μ0 y)) = lam • eR (D.what₂.iota D.what₂.mu0 (cF (cpt σ y)))

def ColNormT : Prop :=
  ∀ u, ∃ c : ℝ, 0 < c ∧ ∀ φ : D.what₂.Mu u, Formalism.DivisionValues.fnorm ((fc P.zs).Dc.Xc (m u) Bs.v0) (cjv s (cφ u φ)) = c * ‖φ‖

def PairTieT : Prop :=
  ∀ u, ∃ κ : ℂ, κ ≠ 0 ∧ ∀ (F : D.what₂.EE) (φ : D.what₂.Mu u) (T : Cu X u hK),
    colDictL X (Tr u) hK T = ((D.eMu u φ : (D.mem u).A.Mram) : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ) →
      ⟪sEE (eR F), (fc P.zs).Sp.Pu (m u) (cjv s (cφ u φ))⟫_ℂ =
        Formalism.IndefR.Links.cj s (κ * ⟪((conjHH X G (j F) : HHX X) : L2X X), PuFun X u hK (Dt u) T⟫_ℂ)

theorem exists_conj_op (hR : RowTieT P eV s σ cF eR) (V : P.EE →ₗ[ℂ] P.EE) (hV : ∀ e ∈ P.EEl true, V e ∈ P.EEl true) :
    ∃ V1 : D.what₂.EE →ₗ[ℂ] D.what₂.EE, ∀ F, eR (V1 F) = V (eR F) := by
  obtain ⟨h1, h2, ⟨c, hc, hn⟩, -⟩ := hR
  have hinj : Function.Injective eR := by
    intro a b hab
    have h0 : ‖eR (a - b)‖ = 0 := by rw [map_sub, hab, sub_self, norm_zero]
    rw [hn, mul_eq_zero] at h0
    rcases h0 with h | h
    · exact absurd h hc.ne'
    · exact sub_eq_zero.1 (norm_eq_zero.1 h)
  have hex : ∀ F, ∃ F', eR F' = V (eR F) := fun F => h2 _ (hV _ (h1 F))
  choose g hg using hex
  refine ⟨⟨⟨g, ?_⟩, ?_⟩, hg⟩
  · intro a b
    apply hinj
    simp only [hg, map_add]
  · intro r a
    apply hinj
    simp only [hg, map_smulₛₗ, RingHom.id_apply]

theorem kerJoinS_of_miT (hs : ∀ a, Bs.v0.embedding a = Formalism.IndefR.Links.cj s (σ a)) (hM : P.MIstar eV sEE)
    (hC : ChainTieT (P := P) (σ := σ) (m := m) (cφ := cφ) (cF := cF))
    (hV : GoodPartHasComplexCoordinates (P := P) (fc := fc) (cF := cF))
    (hR : RowTieT (P := P) (fc := fc) (eV := eV) (s := s) (σ := σ) (cF := cF) (eR := eR))
    (hN : ColNormT (P := P) (s := s) (m := m) (cφ := cφ))
    (hP : PairTieT (X := X) (G := G) (j := j) (Tr := Tr) (hK := hK) (Dt := Dt) (P := P) (fc := fc) (sEE := sEE) (s := s) (m := m)
      (cφ := cφ) (eR := eR)) :
    KerJoinS X G j Tr hK Dt := by
  classical
  obtain ⟨d, hUn, hI, hA⟩ := hM
  obtain ⟨V1, hV1⟩ := exists_conj_op (P := P) (fc := fc) (eV := eV) (s := s) (σ := σ) (cF := cF) (eR := eR) hR d.V (fun e he => (hUn.1 e he).1)
  obtain ⟨hRin, -, ⟨c, hc, hcn⟩, lam, hlam, hRΘ⟩ := hR
  have hV1n : ∀ F, ‖V1 F‖ = ‖F‖ := by
    intro F
    have h1 : c * ‖V1 F‖ = c * ‖F‖ := by
      rw [← hcn, ← hcn, hV1]
      exact (hUn.1 _ (hRin F)).2
    exact mul_left_cancel₀ hc.ne' h1
  let V1i : D.what₂.EE →ₗᵢ[ℂ] D.what₂.EE := { toLinearMap := V1, norm_map' := hV1n }
  refine ⟨V1i.toLinearIsometryEquiv rfl, fun u => ?_⟩
  obtain ⟨κ, hκ, hPu⟩ := hP u
  obtain ⟨cu, hcu, hcun⟩ := hN u
  let Mu := d.U (m u)
  let U1 : D.what₂.Mu u →ₗ[ℂ] D.what₂.Mu u :=
    { toFun := fun φ => (cφ u).symm (cjv s (Mu.mulVec (cjv s (cφ u φ))))
      map_add' := fun φ ψ => by
        simp only [map_add, cjv_add, Matrix.mulVec_add]
      map_smul' := fun r φ => by
        simp only [map_smul, cjv_smul, Matrix.mulVec_smul, Formalism.IndefR.Links.cj_cj, RingHom.id_apply] }
  have hU1 : ∀ φ, cjv s (cφ u (U1 φ)) = Mu.mulVec (cjv s (cφ u φ)) := by
    intro φ
    show cjv s (cφ u ((cφ u).symm _)) = _
    rw [LinearEquiv.apply_symm_apply, cjv_cjv]
  have hU1n : ∀ φ, ‖U1 φ‖ = ‖φ‖ := by
    intro φ
    have h1 : cu * ‖U1 φ‖ = cu * ‖φ‖ := by
      rw [← hcun, ← hcun, hU1]
      exact hUn.2.1 (m u) (cjv s (cφ u φ))
    exact mul_left_cancel₀ hcu.ne' h1
  let U1i : D.what₂.Mu u →ₗᵢ[ℂ] D.what₂.Mu u := { toLinearMap := U1, norm_map' := hU1n }
  have hcjne : Formalism.IndefR.Links.cj s (d.a (m u) * lam) ≠ 0 := (map_ne_zero _).2 (mul_ne_zero (hA (m u)) hlam)
  refine ⟨Formalism.IndefR.Links.cj s (d.a (m u) * lam) * κ, mul_ne_zero hcjne hκ, U1i.toLinearIsometryEquiv rfl,
    fun φ F hF T hT => ?_⟩
  let S : (Fin ((fc P.zs).Df1.nV Bs.μ0) → ℂ) → (fc P.zs).Sp.HH :=
    fun y => sEE (d.V (eR (D.what₂.iota D.what₂.mu0 (cF y))))
  let Q : (Fin ((fc P.zs).Dc.a (m u)) → ℂ) → (fc P.zs).Sp.HH := fun x => (fc P.zs).Sp.Pu (m u) (Mu.mulVec (cjv s x))
  let B2 : (Fin ((fc P.zs).Dc.a (m u)) → ℂ) →ₗ[ℂ] (Fin ((fc P.zs).Df1.nV Bs.μ0) → ℂ) →ₗ[ℂ] ℂ :=
    LinearMap.mk₂ ℂ (fun x y => Formalism.IndefR.Links.cj s (d.a (m u) * lam * ⟪S y, Q x⟫_ℂ))
      (fun x x' y => by
        simp only [Q, cjv_add, Matrix.mulVec_add, map_add, inner_add_right, mul_add])
      (fun r x y => by
        simp only [Q, cjv_smul, Matrix.mulVec_smul, map_smul, inner_smul_right, smul_eq_mul, map_mul,
          Formalism.IndefR.Links.cj_cj]
        ring)
      (fun x y y' => by
        simp only [S, map_add, inner_add_left, mul_add])
      (fun r x y => by
        simp only [S, map_smul, LinearMap.map_smulₛₗ, inner_smul_left, smul_eq_mul, map_mul,
          Formalism.IndefR.Links.cj_cj, starRingEnd_self_apply]
        ring)
  let B1 : (Fin ((fc P.zs).Dc.a (m u)) → ℂ) →ₗ[ℂ] (Fin ((fc P.zs).Df1.nV Bs.μ0) → ℂ) →ₗ[ℂ] ℂ :=
    (perColL D u).compl₁₂ (cφ u).symm.toLinearMap cF
  have hbas : ∀ (i : Fin ((fc P.zs).Dc.a (m u))) (k : Fin ((fc P.zs).Df1.nV Bs.μ0)),
      B1 (Pi.single i 1) (Pi.single k 1) = B2 (Pi.single i 1) (Pi.single k 1) := by
    intro i k
    have hx := Formalism.IndefR.Cx.cpt_single σ i
    have hy := Formalism.IndefR.Cx.cpt_single σ k
    have hx0 := Formalism.IndefR.Cx.cpt_single Bs.v0.embedding i
    show perColL D u ((cφ u).symm (Pi.single i 1)) (cF (Pi.single k 1)) =
      Formalism.IndefR.Links.cj s (d.a (m u) * lam * ⟪sEE (d.V (eR (D.what₂.iota D.what₂.mu0 (cF (Pi.single k 1))))),
        (fc P.zs).Sp.Pu (m u) (Mu.mulVec (cjv s (Pi.single i 1)))⟫_ℂ)
    have L : perColL D u ((cφ u).symm (Pi.single i 1)) (cF (Pi.single k 1)) =
        σ ((fc P.zs).Dc.Pt (m u) Bs.μ0 (Pi.single i 1) (Pi.single k 1)) := by
      rw [perColL_apply]
      have h0 := hC u (Pi.single i 1) (Pi.single k 1)
      rwa [hx, hy] at h0
    have Rr : eR (D.what₂.iota D.what₂.mu0 (cF (Pi.single k 1))) =
        lam⁻¹ • P.Θ Bs.μ0 (P.jR Bs.μ0 (eV Bs.μ0 (Pi.single k 1))) := by
      have h0 := hRΘ (Pi.single k 1)
      rw [hy] at h0
      rw [h0, smul_smul, inv_mul_cancel₀ hlam, one_smul]
    have hin : ∀ (z : P.EE) (w : (fc P.zs).Sp.HH), ⟪sEE (d.V (lam⁻¹ • z)), w⟫_ℂ = lam⁻¹ * ⟪sEE (d.V z), w⟫_ℂ := by
      intro z w
      rw [map_smul, LinearMap.map_smulₛₗ, inner_smul_left, starRingEnd_self_apply]
    rw [L, Rr, hin, mul_assoc (d.a (m u)), mul_inv_cancel_left₀ hlam, cjv_single, ← hx0]
    have h := hI (m u) Bs.μ0 (Pi.single i 1) (Pi.single k 1)
    rw [hUn.2.2.2 (m u), one_mul] at h
    rw [← h, hs, Formalism.IndefR.Links.cj_cj]
  have hall : ∀ x y, B1 x y = B2 x y := by
    intro x y
    rw [Formalism.IndefR.Cx.bil_expand B1, Formalism.IndefR.Cx.bil_expand B2]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    rw [hbas i k]
  obtain ⟨y, rfl⟩ := LinearMap.mem_range.1 (hV hF)
  have hT' := hPu (V1 (D.what₂.iota D.what₂.mu0 (cF y))) (U1 φ) T hT
  have e1 : D.what₂.perCol u D.what₂.mu0 φ (cF y) = B2 (cφ u φ) y := by
    rw [← hall]
    show _ = perColL D u ((cφ u).symm (cφ u φ)) (cF y)
    rw [LinearEquiv.symm_apply_apply, perColL_apply]
  rw [e1]
  show Formalism.IndefR.Links.cj s (d.a (m u) * lam * ⟪sEE (d.V (eR (D.what₂.iota D.what₂.mu0 (cF y)))),
      (fc P.zs).Sp.Pu (m u) (Mu.mulVec (cjv s (cφ u φ)))⟫_ℂ) = _
  rw [← hV1, ← hU1, hT', map_mul (Formalism.IndefR.Links.cj s) (d.a (m u) * lam), Formalism.IndefR.Links.cj_cj, mul_assoc]
  rfl

theorem fnorm_conj {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) :
    Formalism.DivisionValues.fnorm (Y.map (starRingEnd ℂ)) (fun i => starRingEnd ℂ (x i)) = Formalism.DivisionValues.fnorm Y x := by
  have e1 : ∀ M : Matrix (Fin n) (Fin n) ℂ, M.map (starRingEnd ℂ) = (Matrix.conjTranspose M).transpose := by
    intro M
    ext i k
    simp [Matrix.conjTranspose_apply]
  have hinv : (Y.map (starRingEnd ℂ))⁻¹ = Y⁻¹.map (starRingEnd ℂ) := by
    rw [e1, e1, Matrix.conjTranspose_nonsing_inv, Matrix.transpose_nonsing_inv]
  unfold Formalism.DivisionValues.fnorm Formalism.HermitianLatticesTheory.cnorm
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hinv, show (fun i => starRingEnd ℂ (x i)) = (starRingEnd ℂ) ∘ x from rfl, ← RingHom.map_mulVec,
    Complex.norm_conj]

theorem fnorm_cjv (s : Bool) {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) :
    Formalism.DivisionValues.fnorm (Y.map (Formalism.IndefR.Links.cj s)) (cjv s x) = Formalism.DivisionValues.fnorm Y x := by
  cases s with
  | false =>
    have h1 : Y.map (Formalism.IndefR.Links.cj false) = Y := by
      ext i k
      simp [Formalism.IndefR.Links.cj]
    have h2 : cjv false x = x := by
      funext i
      simp [cjv, Formalism.IndefR.Links.cj]
    rw [h1, h2]
  | true => exact fnorm_conj Y x

end Twist

section SpOf

open Formalism.IndefR.Cx in

theorem inner_spOf {D : D7} {X : HidaSetting D} (s : Bool) {Bs : DefBase D.what₂.LL} {Df : DefSide Bs} (Dc : DefCols Df)
    (hK : X.LevelSubgroupCharacter) (Gd : GoodOp X) (wdD : Dc.Mem → D.what₂.Word) (pw : ∀ x, PerW X hK (wdD x))
    (bR : ∀ x, Fin (Dc.a x) → (D.mem (wdD x)).A.Mram) (x : Dc.Mem) (v : Formalism.IndefR.Links.Tw s (HHX X))
    (c : Fin (Dc.a x) → ℂ) :
    ⟪v, (spOf s Dc hK Gd wdD pw bR).Pu x (cjv s c)⟫_ℂ =
      Formalism.IndefR.Links.cj s ⟪Formalism.IndefR.Links.Tw.out v, (pw x).op (ramCrd (bR x) c)⟫_ℂ := by
  have hc : cjVec s (Dc.a x) (cjv s c) = c := by
    funext i; exact Formalism.IndefR.Links.cj_cj s (c i)
  have h : (pw x).op (ramCrd (bR x) (cjVec s (Dc.a x) (cjv s c))) = (pw x).op (ramCrd (bR x) c) := by rw [hc]
  exact congrArg (fun w => Formalism.IndefR.Links.cj s ⟪Formalism.IndefR.Links.Tw.out v, w⟫_ℂ) h

open Formalism.IndefR.Cx in

theorem inner_spOf_pin {D : D7} {X : HidaSetting D} (s : Bool) {Bs : DefBase D.what₂.LL} {Df : DefSide Bs} (Dc : DefCols Df)
    (hK : X.LevelSubgroupCharacter) (Gd : GoodOp X) (wdD : Dc.Mem → D.what₂.Word) (pw : ∀ x, PerW X hK (wdD x))
    (bR : ∀ x, Fin (Dc.a x) → (D.mem (wdD x)).A.Mram) (x : Dc.Mem) (v : Formalism.IndefR.Links.Tw s (HHX X))
    (c : Fin (Dc.a x) → ℂ) (G : GoodOp X) (F : EEC X G) (κ₀ : ℂ)
    (hv : Formalism.IndefR.Links.Tw.out v = κ₀ • conjHH X G F) (T : Cu X (wdD x) hK)
    (hT : colDictL X (pw x).Tr hK T =
      (((ramCrd (bR x) c : (D.mem (wdD x)).A.Mu0)) : (D.mem (wdD x)).C.cls 0 → (D.mem (wdD x)).C.Y 0 → ℂ)) :
    ⟪v, (spOf s Dc hK Gd wdD pw bR).Pu x (cjv s c)⟫_ℂ =
      Formalism.IndefR.Links.cj s (starRingEnd ℂ κ₀ * ⟪((conjHH X G F : HHX X) : L2X X), PuFun X (wdD x) hK (pw x).Dt T⟫_ℂ) := by
  rw [inner_spOf, hv, inner_smul_left]
  have hd : (colDict X (pw x).Tr hK (pw x).hI (pw x).hB).symm (ramCrd (bR x) c) = T := by
    rw [LinearEquiv.symm_apply_eq]
    exact Subtype.ext hT.symm
  have hop : (pw x).op (ramCrd (bR x) c) =
      Formalism.L2.SG.PoincareInHH.PoincareSetting.Pu X (wdD x) hK (pw x).Dt (pw x).hD (pw x).hin (pw x).hlin T := by
    show Formalism.L2.SG.PoincareInHH.PoincareSetting.Pu X (wdD x) hK (pw x).Dt (pw x).hD (pw x).hin (pw x).hlin
      ((colDict X (pw x).Tr hK (pw x).hI (pw x).hB).symm (ramCrd (bR x) c)) = _
    rw [hd]
  rw [hop]
  rfl

end SpOf

section At

theorem twist_of_mk {K : Type} [Field K] (σ : K →+* ℂ) (v : NumberField.InfinitePlace K)
    (h : v = NumberField.InfinitePlace.mk σ) (a : K) :
    v.embedding a = Formalism.IndefR.Links.cj (Formalism.IndefR.Links.twAt σ v) (σ a) := by
  subst h
  have hs : Formalism.IndefR.Links.sgAt σ (NumberField.InfinitePlace.mk σ) = σ := by
    unfold Formalism.IndefR.Links.sgAt
    exact if_pos rfl
  unfold Formalism.IndefR.Links.twAt
  rw [hs]
  split_ifs with h1
  · simp [Formalism.IndefR.Links.cj, h1]
  · rcases NumberField.InfinitePlace.embedding_mk_eq σ with h2 | h2
    · exact absurd h2 h1
    · simp [Formalism.IndefR.Links.cj, h2]

variable {D : D7}

structure JoinAt (X : HidaSetting D) (G : GoodOp X) (Y : Formalism.L2.SG.Full.Full X)
    (j : FinX Y → (D.what₂.EE ≃ₗᵢ[ℂ] EEC X G)) {Fm : ∀ u, Formalism.L2.Forms.Forms0 D u} (Tr : ∀ u, Transport X u (Fm u))
    {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs}
    (P : CxData A) (fc : DefSub A → DefFace Bs)
    (eV : ∀ t, (Fin ((fc P.zs).Df1.nV t) → K) →ₗ[K] A.FR t) (sEE : P.EE →ₗ⋆[ℂ] (fc P.zs).Sp.HH)
    (s : Bool) (σ : K →+* ℂ) where

  m : D.what₂.Word → (fc P.zs).Dc.Mem

  cφ : ∀ u, D.what₂.Mu u ≃ₗ[ℂ] (Fin ((fc P.zs).Dc.a (m u)) → ℂ)

  cF : (Fin ((fc P.zs).Df1.nV Bs.μ0) → ℂ) →ₗ[ℂ] D.what₂.Amb D.what₂.mu0

  eR : D.what₂.EE →ₛₗ[Formalism.IndefR.Links.cj s] P.EE

  twist : ∀ a, Bs.v0.embedding a = Formalism.IndefR.Links.cj s (σ a)

  chainTie : ChainTieT (P := P) (fc := fc) (σ := σ) (m := m) (cφ := cφ) (cF := cF)

  v0Surjective : GoodPartHasComplexCoordinates (P := P) (fc := fc) (cF := cF)

  rowTie : RowTieT (P := P) (fc := fc) (eV := eV) (s := s) (σ := σ) (cF := cF) (eR := eR)

  colNorm : ColNormT (P := P) (fc := fc) (s := s) (m := m) (cφ := cφ)

  pairTie : ∀ hF : FinX Y, PairTieT (X := X) (G := G) (j := j hF) (Tr := Tr) (hK := Y.hK) (Dt := Y.Dt)
    (P := P) (fc := fc) (sEE := sEE) (s := s) (m := m) (cφ := cφ) (eR := eR)

variable {X : HidaSetting D} {G : GoodOp X} {Y : Formalism.L2.SG.Full.Full X} {j : FinX Y → (D.what₂.EE ≃ₗᵢ[ℂ] EEC X G)}
  {Fm : ∀ u, Formalism.L2.Forms.Forms0 D u} {Tr : ∀ u, Transport X u (Fm u)}
  {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs}
  {P : CxData A} {fc : DefSub A → DefFace Bs}
  {eV : ∀ t, (Fin ((fc P.zs).Df1.nV t) → K) →ₗ[K] A.FR t} {sEE : P.EE →ₗ⋆[ℂ] (fc P.zs).Sp.HH}
  {s : Bool} {σ : K →+* ℂ}

theorem kerJoinS_of_joinAt (hM : P.MIstar eV sEE) (J : JoinAt X G Y j Tr P fc eV sEE s σ) (hF : FinX Y) :
    KerJoinS X G (j hF) Tr Y.hK Y.Dt := kerJoinS_of_miT (X := X) (G := G) (j := j hF) (Tr := Tr) (hK := Y.hK) (Dt := Y.Dt)
    (hs := J.twist) (hM := hM) (hC := J.chainTie) (hV := J.v0Surjective) (hR := J.rowTie) (hN := J.colNorm) (hP := J.pairTie hF)

theorem admissible_of_join (hM : P.MIstar eV sEE) (J : JoinAt X G Y j Tr P fc eV sEE s σ) (hF : FinX Y)
    (I : SIso D.s (Formalism.L2.SG.PackageTie2.sOf hF))
    (hRow : ∀ F, I.eHH (D.sEE F) = conjHH X G (j hF F)) (hCol : ColJoinS hF I Tr) (hB : Formalism.BasicNotions.Rows.BuDefQ D.what₂)
    (hon : (D.what₂.V0 D.what₂.mu0).map (D.what₂.iota D.what₂.mu0) = ⊤) : Formalism.MainNotions.LocalQuadraticParts.adm13 D :=
  besselId_of_joins hF I Tr G (j hF) hRow hCol (kerJoinS_of_joinAt hM J hF) hB hon

end At

section Ties

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {Kc : MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {R : Formalism.L2.RecT ex}

def jOf (S : Formalism.L2.SG.SpectralTiesReal.STiesR R) (hF : FinX S.Y) : D.what₂.EE ≃ₗᵢ[ℂ] EEC S.X S.G :=
  Classical.choose (S.rowTie hF)

theorem jOf_spec (S : Formalism.L2.SG.SpectralTiesReal.STiesR R) (hF : FinX S.Y) (F : D.what₂.EE) :
    (S.hI hF).eHH (D.sEE F) = conjHH S.X S.G (jOf S hF F) := Classical.choose_spec (S.rowTie hF) F

theorem jOf_eq (S : Formalism.L2.SG.SpectralTiesReal.STiesR R) (hF : FinX S.Y) (j : D.what₂.EE ≃ₗᵢ[ℂ] EEC S.X S.G)
    (hj : ∀ F, (S.hI hF).eHH (D.sEE F) = conjHH S.X S.G (j F)) : jOf S hF = j := by
  apply LinearIsometryEquiv.ext
  intro F
  apply (conjHH S.X S.G).injective
  rw [← jOf_spec S hF F]
  exact hj F

theorem colJoinS_of_sTiesR (S : Formalism.L2.SG.SpectralTiesReal.STiesR R) (hF : FinX S.Y) : ColJoinS hF (S.hI hF) S.tr :=
  colJoinS_of_pin hF (S.hI hF) S.tr S.into S.bij fun u x =>
    (LinearEquiv.eq_symm_apply (colDict S.X (S.tr u) S.Y.hK (S.into u) (S.bij u))).2 (S.colPin hF u x)

theorem admissible_of_transported_ties (S : Formalism.L2.SG.SpectralTiesReal.STiesR R)
    {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs}
    {P' : CxData A} {fc : DefSub A → DefFace Bs}
    {eV : ∀ t, (Fin ((fc P'.zs).Df1.nV t) → K) →ₗ[K] A.FR t} {sEE : P'.EE →ₗ⋆[ℂ] (fc P'.zs).Sp.HH} {s : Bool} {σ : K →+* ℂ}
    (hM : P'.MIstar eV sEE) (J : JoinAt S.X S.G S.Y (jOf S) S.tr P' fc eV sEE s σ) (hF : FinX S.Y)
    (hon : (D.what₂.V0 D.what₂.mu0).map (D.what₂.iota D.what₂.mu0) = ⊤) : Formalism.MainNotions.LocalQuadraticParts.adm13 D := admissible_of_join hM J hF (S.hI hF) (jOf_spec S hF) (colJoinS_of_sTiesR S hF) R.pin.buDef hon

end Ties

section Real

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {Kc : MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}

abbrev cx {R : Formalism.L2.RecT ex} {P : Formalism.L2.Rows.RowSideFamily ex}
    {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)} {Spf : ∀ Zs, SPer (Dcf Zs)}
    {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3} {S : Formalism.L2.SG.SpectralTiesReal.STiesR R}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Q : Formalism.IndefR.RealT R P Dcf Spf Zscf S Ks) :=
  Q.Rl.toCx3 Q.F

abbrev twQ (P : Formalism.L2.Rows.RowSideFamily ex) : Bool :=
  Formalism.IndefR.Links.twAt D.what₂.embLL P.A3.A.v0

structure JoinSI (R : Formalism.L2.RecT ex) (S : Formalism.L2.SG.SpectralTiesReal.STiesR R) {P : Formalism.L2.Rows.RowSideFamily ex}
    {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)} {Spf : ∀ Zs, SPer (Dcf Zs)}
    {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (Q : Formalism.IndefR.RealT R P Dcf Spf Zscf S Ks) where

  m : D.what₂.Word → (Q.F.fc (cx Q).zs).Dc.Mem

  mPin : HEq m P.I.wU

  cφ : ∀ u, D.what₂.Mu u ≃ₗ[ℂ] (Fin ((Q.F.fc (cx Q).zs).Dc.a (m u)) → ℂ)

  cF : (Fin ((Q.F.fc (cx Q).zs).Df1.nV P.A3.fam3.base3.μ0) → ℂ) →ₗ[ℂ] D.what₂.Amb D.what₂.mu0

  eR : D.what₂.EE →ₛₗ[Formalism.IndefR.Links.cj (twQ P)] (cx Q).EE

  chainTie : ChainTieT (P := cx Q) (fc := Q.F.fc) (σ := D.what₂.embLL) (m := m) (cφ := cφ) (cF := cF)

  v0Surjective : GoodPartHasComplexCoordinates (P := cx Q) (fc := Q.F.fc) (cF := cF)

  rowTie : RowTieT (P := cx Q) (fc := Q.F.fc) (eV := Q.F.eV (cx Q).zs) (s := twQ P) (σ := D.what₂.embLL) (cF := cF) (eR := eR)

  colNorm : ColNormT (P := cx Q) (fc := Q.F.fc) (s := twQ P) (m := m) (cφ := cφ)

  pairTie : ∀ hF : FinX S.Y, PairTieT (X := S.X) (G := S.G) (j := jOf S hF) (Tr := S.tr) (hK := S.Y.hK) (Dt := S.Y.Dt)
    (P := cx Q) (fc := Q.F.fc) (sEE := Q.sEE) (s := twQ P) (m := m) (cφ := cφ) (eR := eR)

variable {R : Formalism.L2.RecT ex} {S : Formalism.L2.SG.SpectralTiesReal.STiesR R} {P : Formalism.L2.Rows.RowSideFamily ex}
  {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)} {Spf : ∀ Zs, SPer (Dcf Zs)}
  {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  {Q : Formalism.IndefR.RealT R P Dcf Spf Zscf S Ks}

theorem twist_of_realT (Q : Formalism.IndefR.RealT R P Dcf Spf Zscf S Ks) (a : D.what₂.LL) :
    P.A3.fam3.base3.v0.embedding a = Formalism.IndefR.Links.cj (twQ P) (D.what₂.embLL a) := by
  first
  | exact twist_of_mk D.what₂.embLL _ Q.Rl.hv0 a
  | exact twist_of_mk D.what₂.embLL _ Q.Rl.hv0.symm a
  | exact twist_of_mk D.what₂.embLL _ Q.hv0 a
  | exact twist_of_mk D.what₂.embLL _ Q.hv0.symm a
  | exact twist_of_mk D.what₂.embLL _ Q.Rl.toRealDat.hv0 a

def JoinSI.toJoinAt (J : JoinSI R S Q) :
    JoinAt S.X S.G S.Y (jOf S) S.tr (cx Q) Q.F.fc (Q.F.eV (cx Q).zs) Q.sEE (twQ P) D.what₂.embLL where
  m := J.m
  cφ := J.cφ
  cF := J.cF
  eR := J.eR
  twist := twist_of_realT Q
  chainTie := J.chainTie
  v0Surjective := J.v0Surjective
  rowTie := J.rowTie
  colNorm := J.colNorm
  pairTie := J.pairTie

theorem kerJoinS_of_joinSI (hM : (cx Q).MIstar (Q.F.eV (cx Q).zs) Q.sEE) (J : JoinSI R S Q) (hF : FinX S.Y) :
    KerJoinS S.X S.G (jOf S hF) S.tr S.Y.hK S.Y.Dt := kerJoinS_of_joinAt hM J.toJoinAt hF

theorem admissible_of_kernelJoin (hM : (cx Q).MIstar (Q.F.eV (cx Q).zs) Q.sEE) (J : JoinSI R S Q) (hF : FinX S.Y)
    (hon : (D.what₂.V0 D.what₂.mu0).map (D.what₂.iota D.what₂.mu0) = ⊤) : Formalism.MainNotions.LocalQuadraticParts.adm13 D := admissible_of_transported_ties S hM J.toJoinAt hF hon

end Real

end Formalism.L2.SG.JoinSI
