import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.JoinSI
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.KerSideCut
import Formalism.LocalToGlobal.IndefiniteReal.IsometricPeriodsOfHypotheses
import Formalism.LocalToGlobal.IndefiniteReal.IsometricPeriodsOfUnitHypotheses

open scoped InnerProductSpace
open MeasureTheory Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.RowDict Formalism.L2.SG.ColDict Formalism.L2.SG.KerJoinS Formalism.L2.SG.KerSideCut Formalism.IndefR.Cx Formalism.L2.Indef

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

theorem kernelJoin_of_multiplicity (hs : ∀ a, Bs.v0.embedding a = Formalism.IndefR.Links.cj s (σ a)) (hM : P.MIstar2 eV sEE)
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

end Twist

section At

variable {D : D7}

variable {X : HidaSetting D} {G : GoodOp X} {Y : Formalism.L2.SG.Full.Full X} {j : FinX Y → (D.what₂.EE ≃ₗᵢ[ℂ] EEC X G)}
  {Fm : ∀ u, Formalism.L2.Forms.Forms0 D u} {Tr : ∀ u, Transport X u (Fm u)}
  {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs}
  {P : CxData A} {fc : DefSub A → DefFace Bs}
  {eV : ∀ t, (Fin ((fc P.zs).Df1.nV t) → K) →ₗ[K] A.FR t} {sEE : P.EE →ₗ⋆[ℂ] (fc P.zs).Sp.HH}
  {s : Bool} {σ : K →+* ℂ}

theorem kerJoinS_of_joinAt2 (hM : P.MIstar2 eV sEE) (J : JoinAt X G Y j Tr P fc eV sEE s σ) (hF : FinX Y) :
    KerJoinS X G (j hF) Tr Y.hK Y.Dt :=
  kernelJoin_of_multiplicity X G (j hF) Tr Y.hK Y.Dt P eV sEE s σ J.m J.cφ J.cF J.eR J.twist hM
    J.chainTie J.v0Surjective J.rowTie J.colNorm (J.pairTie hF)

theorem adm13_of_colJoin (hM : P.MIstar2 eV sEE) (J : JoinAt X G Y j Tr P fc eV sEE s σ) (hF : FinX Y)
    (I : SIso D.s (Formalism.L2.SG.PackageTie2.sOf hF))
    (hRow : ∀ F, I.eHH (D.sEE F) = conjHH X G (j hF F)) (hCol : ColJoinS hF I Tr) (hB : Formalism.BasicNotions.Rows.BuDefQ D.what₂)
    (hon : (D.what₂.V0 D.what₂.mu0).map (D.what₂.iota D.what₂.mu0) = ⊤) : Formalism.MainNotions.LocalQuadraticParts.adm13 D :=
  besselId_of_joins hF I Tr G (j hF) hRow hCol (kerJoinS_of_joinAt2 hM J hF) hB hon

end At

section Ties

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {Kc : MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {R : Formalism.L2.RecT ex}

theorem adm13_of_joinAt (S : Formalism.L2.SG.SpectralTiesReal.STiesR R)
    {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs}
    {P' : CxData A} {fc : DefSub A → DefFace Bs}
    {eV : ∀ t, (Fin ((fc P'.zs).Df1.nV t) → K) →ₗ[K] A.FR t} {sEE : P'.EE →ₗ⋆[ℂ] (fc P'.zs).Sp.HH} {s : Bool} {σ : K →+* ℂ}
    (hM : P'.MIstar2 eV sEE) (J : JoinAt S.X S.G S.Y (jOf S) S.tr P' fc eV sEE s σ) (hF : FinX S.Y)
    (hon : (D.what₂.V0 D.what₂.mu0).map (D.what₂.iota D.what₂.mu0) = ⊤) : Formalism.MainNotions.LocalQuadraticParts.adm13 D :=
  adm13_of_colJoin hM J hF (S.hI hF) (jOf_spec S hF) (colJoinS_of_sTiesR S hF) R.pin.buDef hon

end Ties

section Real

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {Kc : MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}

variable {R : Formalism.L2.RecT ex} {S : Formalism.L2.SG.SpectralTiesReal.STiesR R} {P : Formalism.L2.Rows.RowSideFamily ex}
  {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)} {Spf : ∀ Zs, SPer (Dcf Zs)}
  {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  {Q : Formalism.IndefR.RealT R P Dcf Spf Zscf S Ks}

theorem adm13_of_joinSI (hM : (cx Q).MIstar2 (Q.F.eV (cx Q).zs) Q.sEE) (J : JoinSI R S Q) (hF : FinX S.Y)
    (hon : (D.what₂.V0 D.what₂.mu0).map (D.what₂.iota D.what₂.mu0) = ⊤) : Formalism.MainNotions.LocalQuadraticParts.adm13 D :=
  adm13_of_joinAt S hM J.toJoinAt hF hon

end Real

end Formalism.L2.SG.JoinSI
