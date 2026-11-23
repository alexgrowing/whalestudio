import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.PrimitiveStatementsWithPassage

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Cx

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.L2.Col

variable {K : Type} [Field K] [NumberField K] [StarRing K]

section Concrete3

variable {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}

variable {A3 : FamIn3 K G Pl0 I0 Ty T m} {P0 : Subgroup G} {ψ0 : P0 →* Kˣ} {P1 : Subgroup G} {ψ1 : P1 →* Kˣ}
  {Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 P1 ψ1 Zs)} {Sp : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dc Zs)}
  {Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3}

theorem definite_coordinates_in_subspaces (X : CxData A3.fam3.amb3) (b : Bool) : X.CrdZ (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) b := by
  intro t x
  cases b <;> exact toF_mem_Z _ _ _

theorem definite_coordinates_in_good_part (X : CxData A3.fam3.amb3) (b : Bool) :
    X.CoordinatesInGoodPart (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) (cvOf3 A3 P0 ψ0 P1 ψ1) b := by
  intro t x
  cases b <;> exact BlockGood.toF_mem_goodR _ _ _ x

theorem lift_coordinates_in_subspaces (X : CxData A3.fam3.amb3) (b : Bool) : X.CrdZL (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) b := by
  intro j t x
  cases b <;> exact toF_mem_Z _ _ _

theorem lift_coordinates_in_good_part_family (X : CxData A3.fam3.amb3) (b : Bool) :
    X.LiftCoordinatesInGoodPart (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) (cvOf3 A3 P0 ψ0 P1 ψ1) b := by
  intro j t x
  cases b <;> exact BlockGood.toF_mem_goodR _ _ _ x

theorem definite_isometry_of_norms {X : CxData A3.fam3.amb3} {s : ℕ} (hok : A3.fam3.Ok3 s) (hJ : X.JIsoR (cvOf3 A3 P0 ψ0 P1 ψ1))
    (hn : X.nP false = (Nat.card P0 : ℝ) ∧ X.nP true = (Nat.card P1 : ℝ)) (b : Bool) : X.IsoR (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) b := by
  intro t x y
  have h2 := hok.ok2
  cases b
  · rw [hJ t, hn.1]
    exact BlockGood.csum_toF_at _ h2.conj (h2.what₂ t) _ h2.irr _ x y
  · rw [hJ t, hn.2]
    exact BlockGood.csum_toF_at _ h2.conj (h2.what₂ t) _ h2.irr _ x y

theorem lift_isometry_of_norms {X : CxData A3.fam3.amb3} {s : ℕ} (hok : A3.fam3.Ok3 s) (hJ : X.JIsoL (cvOf3 A3 P0 ψ0 P1 ψ1))
    (hn : X.nP false = (Nat.card P0 : ℝ) ∧ X.nP true = (Nat.card P1 : ℝ)) (b : Bool) : X.IsoL (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) b := by
  intro j t x y
  have h2 := hok.ok2
  cases b
  · rw [hJ j t, hn.1]
    exact BlockGood.csum_toF_at _ h2.conj (h2.lifts j t) _ h2.irr _ x y
  · rw [hJ j t, hn.2]
    exact BlockGood.csum_toF_at _ h2.conj (h2.lifts j t) _ h2.irr _ x y

theorem definite_adjoint_closed {X : CxData A3.fam3.amb3} {s : ℕ} (hok : A3.fam3.Ok3 s)
    (hH : ∀ t, (A3.A.fam.R t).OkH ∧ (A3.rowI t).InertRationalAdjoint) (hK : X.KFormR)
    (hJ : X.JIsoR (cvOf3 A3 P0 ψ0 P1 ψ1)) : X.AdjClosedR := by
  intro t i
  rcases i with (p | k) | g
  · obtain ⟨p', hp'⟩ := (hH t).1.adj p
    exact ⟨Sum.inl (Sum.inl p'), X.opC_adjoint hK (cvOf3 A3 P0 ψ0 P1 ψ1) hJ t (Sum.inl (Sum.inl p)) (Sum.inl (Sum.inl p'))
      fun f f' => hp' f f'⟩
  · obtain ⟨k', hk'⟩ := (hH t).2.adj k
    exact ⟨Sum.inl (Sum.inr k'), X.opC_adjoint hK (cvOf3 A3 P0 ψ0 P1 ψ1) hJ t (Sum.inl (Sum.inr k)) (Sum.inl (Sum.inr k'))
      fun f f' => hk' f f'⟩
  · exact ⟨Sum.inr g⁻¹, X.opC_adjoint hK (cvOf3 A3 P0 ψ0 P1 ψ1) hJ t (Sum.inr g) (Sum.inr g⁻¹)
      fun f f' => csum_act_inv (hok.ok2.what₂ t).act g f f'⟩

theorem lift_adjoint_closed {X : CxData A3.fam3.amb3} {s : ℕ} (hok : A3.fam3.Ok3 s)
    (hH : ∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint) (hK : X.KFormL)
    (hJ : X.JIsoL (cvOf3 A3 P0 ψ0 P1 ψ1)) : X.AdjClosedL := by
  intro j t i
  rcases i with (p | k) | g
  · obtain ⟨p', hp'⟩ := (hH j t).1.adj p
    exact ⟨Sum.inl (Sum.inl p'), X.opLC_adjoint hK (cvOf3 A3 P0 ψ0 P1 ψ1) hJ j t (Sum.inl (Sum.inl p))
      (Sum.inl (Sum.inl p')) fun f f' => hp' f f'⟩
  · obtain ⟨k', hk'⟩ := (hH j t).2.adj k
    exact ⟨Sum.inl (Sum.inr k'), X.opLC_adjoint hK (cvOf3 A3 P0 ψ0 P1 ψ1) hJ j t (Sum.inl (Sum.inr k))
      (Sum.inl (Sum.inr k')) fun f f' => hk' f f'⟩
  · exact ⟨Sum.inr g⁻¹, X.opLC_adjoint hK (cvOf3 A3 P0 ψ0 P1 ψ1) hJ j t (Sum.inr g) (Sum.inr g⁻¹)
      fun f f' => csum_act_inv (hok.ok2.lifts j t).act g f f'⟩

end Concrete3

section Equiv3

variable {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}
variable {A3 : FamIn3 K G Pl0 I0 Ty T m} {X : CxData A3.fam3.amb3}

theorem coordinates_mem_subspace {B : BlockDat K G Pl0} (ℓ : Lvl K G) (Z : Submodule K B.S.Forms) (y : Fin (B.dZ ℓ Z) → K) :
    B.toF ℓ Z y ∈ Z := by
  exact toF_mem_Z ℓ Z y

theorem part_iff_rows3 (hR : X.KFormR) (hst : X.zs.Stable) {s : ℕ} (hOk : A3.fam3.Ok3 s)
    {hE : ∀ t, (A3.rowI t).OpIx → Module.End ℂ X.EE} (hH : HeckeIntertwiningDefinite A3 X hE) (p : A3.fam3.base3.Ix)
    (ℓ : Lvl K G) (y : Fin ((A3.fam3.F.R A3.fam3.F.μ0).dZ ℓ (X.Z A3.fam3.F.μ0)) → K) :
    y ∈ (A3.fam3.RI A3.fam3.F.μ0).part3 ℓ (X.Z A3.fam3.F.μ0) p.1 ↔
      X.Θ A3.fam3.F.μ0 (X.jR A3.fam3.F.μ0 ((A3.fam3.F.R A3.fam3.F.μ0).toF ℓ (X.Z A3.fam3.F.μ0) y)) ∈ X.EEp p := by
  have : FiniteDimensional K (A3.fam3.F.R A3.fam3.F.μ0).S.Forms := Module.Finite.of_basis (A3.fam3.F.R A3.fam3.F.μ0).S.basis
  rw [InertDat3.inert_part_eq_comap, Submodule.mem_comap, InertDat3.inertTypeEigenspaceSum, hH.parts p]
  exact mem_eigSum_iff_map ((X.Θ A3.fam3.F.μ0).comp (X.jR A3.fam3.F.μ0)) (hOk.what₂ _).comm
    (InertDat3.splitOver_opAll _ (hOk.ok2.what₂ _) (hOk.what₂ _)) hH.comm
    (fun i v => by
      show X.Θ _ (X.jR _ (A3.fam3.amb3.opR _ (Sum.inl i) v)) = _
      rw [X.jR_opR hR, hH.intw]; rfl)
    (DefFam3.stable3_rows hst A3.fam3.F.μ0) (fun z hz h0 => X.theta_jR_inj hR _ z hz h0) _ (coordinates_mem_subspace ℓ _ y)

theorem part_iff_lifts3 (hL : X.KFormL) (hst : X.zs.Stable) {s : ℕ} (hOk : A3.fam3.Ok3 s)
    {hW : ∀ j t, (A3.liftI j t).OpIx → Module.End ℂ (X.W j)} (hH : HeckeIntertwiningLifts A3 X hW) (j : Fin m)
    (p : A3.fam3.base3.Ix) (ℓ : Lvl K G) (y : Fin ((A3.fam3.F.L j A3.fam3.F.μ0).dZ ℓ (X.Zl j A3.fam3.F.μ0)) → K) :
    y ∈ (A3.fam3.LI j A3.fam3.F.μ0).part3 ℓ (X.Zl j A3.fam3.F.μ0) (A3.fam3.tr3 j p.1) ↔
      X.θ' j A3.fam3.F.μ0 (X.jL j A3.fam3.F.μ0 ((A3.fam3.F.L j A3.fam3.F.μ0).toF ℓ (X.Zl j A3.fam3.F.μ0) y)) ∈ X.Wp j p := by
  have : FiniteDimensional K (A3.fam3.F.L j A3.fam3.F.μ0).S.Forms := Module.Finite.of_basis (A3.fam3.F.L j A3.fam3.F.μ0).S.basis
  rw [InertDat3.inert_part_eq_comap, Submodule.mem_comap, InertDat3.inertTypeEigenspaceSum, hH.parts j p]
  exact mem_eigSum_iff_map ((X.θ' j A3.fam3.F.μ0).comp (X.jL j A3.fam3.F.μ0)) (hOk.lifts _ _).comm
    (InertDat3.splitOver_opAll _ (hOk.ok2.lifts _ _) (hOk.lifts _ _))
    (hH.comm j)
    (fun i v => by
      show X.θ' _ _ (X.jL _ _ (A3.fam3.amb3.opL _ _ (Sum.inl i) v)) = _
      rw [X.jL_opL hL, hH.intw]; rfl)
    (DefFam3.stable3_lifts hst j A3.fam3.F.μ0) (fun z hz h0 => X.theta_jL_inj hL j _ z hz h0) _ (coordinates_mem_subspace ℓ _ y)

variable (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (P1 : Subgroup G) (ψ1 : P1 →* Kˣ)
  (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 P1 ψ1 Zs)) (Sp : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dc Zs))
  (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3)

theorem definite_equivariance_of_primitive (hR : X.KFormR) (hst : X.zs.Stable) {s : ℕ} (hOk : A3.fam3.Ok3 s)
    {hE : ∀ t, (A3.rowI t).OpIx → Module.End ℂ X.EE} (hH : HeckeIntertwiningDefinite A3 X hE) (b : Bool) :
    X.H3 (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) b := by
  intro p x
  rw [CxData.iC_cpt_eq]
  cases b
  · exact part_iff_rows3 hR hst hOk hH p (A3.fam3.F.lvl P0 ψ0) x
  · exact part_iff_rows3 hR hst hOk hH p (A3.fam3.F.lvl P1 ψ1) x

theorem lift_equivariance_of_primitive (hL : X.KFormL) (hst : X.zs.Stable) {s : ℕ} (hOk : A3.fam3.Ok3 s)
    {hW : ∀ j t, (A3.liftI j t).OpIx → Module.End ℂ (X.W j)} (hH : HeckeIntertwiningLifts A3 X hW) (b : Bool) :
    X.H3W (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) b := by
  intro j p x
  rw [CxData.tC_cpt_eq]
  cases b
  · exact part_iff_lifts3 hL hst hOk hH j p (A3.fam3.F.lvlA P0 ψ0) x
  · exact part_iff_lifts3 hL hst hOk hH j p (A3.fam3.F.lvlA P1 ψ1) x

end Equiv3

end Formalism.IndefR.Cx
