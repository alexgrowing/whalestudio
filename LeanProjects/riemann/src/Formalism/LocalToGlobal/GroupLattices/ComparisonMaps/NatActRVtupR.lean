import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ValUniqOf
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.RationalPointsLeHolds
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.CastGLSymmBc
import Formalism.SharpRestriction.GrowthBounds.LatticeSystems

noncomputable section

namespace Formalism.L2.G.Cmp

open Formalism.MainNotions.G Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {Tau : Type} [Fintype Tau] {LL : Type} [Field LL] {p : ℕ}

variable (S : StepLevel F E σ J T f bad) (emb : Tau → E →+* ℂ) (embLL : LL →+* ℂ)
  (G : GAtP p) (A : LocAt F E n G) (pos : (Σ v : Fin G.P.nV, Fin (G.P.n' v)) ≃ Tau)
  {V cls : Type} [AddCommGroup V] [Module LL V] (embV : V →ₛₗ[embLL] (cls → Frames (gramC J emb) → ℂ))
  (yc : cls → UPts σ J (FiniteAdeleRing (𝓞 F) F))

def RatInU : Prop := ∀ γ : GL (Fin n) E, γ ∈ UJ (σ : E →+* E) J →
  bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F)

def AdExt : Prop := ∀ x : V, ∃ fa ∈ AdFun S emb, ∀ c, fa (yc c) = embV x c

def PtOne : Prop :=
  ∀ (i : G.comp) (L : G.P.Tup) (g g' : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v)) (x x' : UPts σ J (FiniteAdeleRing (𝓞 F) F)),
    (∀ v, L v = colSpan (G.P.W v) (g v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v))) →
    (∀ v, L v = colSpan (G.P.W v) (g' v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v))) →
    A.IsPt i g x.1 → A.IsPt i g' x'.1 → ∃ κ : S.U, x'.1 = x.1 * κ.1 ∧ (S.chi κ : ℂ) = 1

def EvRatPt : Prop :=
  ∀ (x : V) (c : cls) (γ : GL (Fin n) E), γ ∈ UJ (σ : E →+* E) J → ∀ κ : S.U,
    ∃ Q ∈ VtupR G.P LL, ∀ z z' : Frames (gramC J emb), IsTr (atInf emb γ) z' z →
      evC G.P A.rk pos (gramC J emb) (crdB emb A.B) (MvPolynomial.map embLL Q) z = (S.chi κ : ℂ) * embV x c z'

variable {S emb embLL G A pos embV yc}

theorem ratInU : RatInU (F := F) (σ := σ) (J := J) := fun γ hγ =>
  Formalism.UG.P.rational_points_le_holds F E (Fin n) σ J (FiniteAdeleRing (𝓞 F) F) ⟨γ, hγ, rfl⟩

theorem atInf_one (emb : Tau → E →+* ℂ) : atInf emb ((1 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) = fun _ => 1 := by
  funext τ
  simp [atInf, Matrix.map_one]

theorem isTr_one (z : Frames (gramC J emb)) : IsTr (atInf emb ((1 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)) z z := by
  intro τ
  rw [atInf_one, Matrix.one_mul]

def ptU (hU : RatInU (F := F) (σ := σ) (J := J)) (γ : GL (Fin n) E) (hγ : γ ∈ UJ (σ : E →+* E) J)
    (y : UPts σ J (FiniteAdeleRing (𝓞 F) F)) (κ : S.U) : UPts σ J (FiniteAdeleRing (𝓞 F) F) :=
  ⟨bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * y.1 * κ.1,
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (hU γ hγ) y.2) ((S.U_eq κ.1).1 κ.2).1⟩

theorem valEx_of (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x)) (hU : RatInU (F := F) (σ := σ) (J := J))
    (hA : AdExt S emb embLL embV yc) (hP : PtEx S G A yc) (hO : PtOne S G A) (hR : EvRatPt S emb embLL G A pos embV) :
    ValEx S emb embLL G A pos embV yc := by
  intro x i L hL
  choose g0 hg0 hLg using hL
  let g : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v) := fun v => ((Matrix.isUnit_iff_isUnit_det _).2 (hg0 v)).unit
  have hg : ∀ v, L v = colSpan (G.P.W v) (g v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)) := hLg
  obtain ⟨c, γ, κ, hγ, hpt⟩ := hP i g
  obtain ⟨Q, hQV, hQ⟩ := hR x c γ hγ κ
  obtain ⟨fa, hfa, hfac⟩ := hA x
  let x0 := ptU (S := S) hU γ hγ (yc c) κ
  have key : ∀ z, evC G.P A.rk pos (gramC J emb) (crdB emb A.B) (MvPolynomial.map embLL Q) z = fa x0 z := by
    intro z
    obtain ⟨z', hz'⟩ := frames_tr emb hc γ hγ z
    rw [hQ z z' hz', hfa γ hγ (yc c) x0 κ rfl z z' hz', hfac c]
  refine ⟨Q, hQV, fun g' hg' c' γ' hγ' κ' hpt' z z' hz' => ?_⟩
  let x1 := ptU (S := S) hU γ' hγ' (yc c') κ'
  obtain ⟨κ0, h01, hχ⟩ := hO i L g g' x0 x1 hg hg' hpt hpt'
  have e1 : fa x1 z = (S.chi κ0 : ℂ) * fa x0 z :=
    hfa 1 (Subgroup.one_mem _) x0 x1 κ0 (by rw [map_one, one_mul]; exact h01) z z (isTr_one z)
  have e2 : fa x1 z = (S.chi κ' : ℂ) * fa (yc c') z' := hfa γ' hγ' (yc c') x1 κ' rfl z z' hz'
  rw [key, ← hfac c', ← e2, e1, hχ, one_mul]

theorem valEx_of' (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x)) (hA : AdExt S emb embLL embV yc) (hP : PtEx S G A yc)
    (hO : PtOne S G A) (hR : EvRatPt S emb embLL G A pos embV) : ValEx S emb embLL G A pos embV yc :=
  valEx_of hc ratInU hA hP hO hR

variable (S emb embLL G A pos embV yc) in

def EvRatRep : Prop :=
  ∀ (x : V) (c : cls), ∃ Q ∈ VtupR G.P LL, ∀ z : Frames (gramC J emb),
    evC G.P A.rk pos (gramC J emb) (crdB emb A.B) (MvPolynomial.map embLL Q) z = embV x c z

variable (S embLL) in

def ChiRatAll : Prop := ∀ κ : S.U, ∃ r : LL, embLL r = (S.chi κ : ℂ)

variable (G A pos) in

def VtupStab (tE : Tau → E →+* LL) : Prop :=
  ∀ γ : GL (Fin n) E, γ ∈ UJ (σ : E →+* E) J → ∀ Q ∈ VtupR G.P LL,
    natActR G.P LL (blkLL A σ tE pos γ) Q ∈ VtupR G.P LL

section Stab

variable {p' : ℕ} {O' Kf' : Type} [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Field Kf'] [Algebra O' Kf']
  (P : Places p' O' Kf')

theorem substR_rename (R : Type) [CommRing R] (h : ∀ v, Fin (P.n' v) → Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) R)
    (v : Fin P.nV) (F : MvPolynomial (Fin (P.n' v) × (Fin (P.m + 1) × Fin (P.m + 1))) R) :
    substR P R h (MvPolynomial.rename (fun x => (⟨v, x⟩ : Var P)) F) =
      MvPolynomial.rename (fun x => (⟨v, x⟩ : Var P)) (Formalism.GradedWeylDivisibility.blockAct R (h v) F) := by
  have e : (substR P R h).comp (MvPolynomial.rename (fun x => (⟨v, x⟩ : Var P))) =
      (MvPolynomial.rename (fun x => (⟨v, x⟩ : Var P))).comp (Formalism.GradedWeylDivisibility.blockAct R (h v)) := by
    apply MvPolynomial.algHom_ext
    intro x
    simp [substR, Formalism.GradedWeylDivisibility.blockAct, map_sum]
  exact congrArg (fun f => f F) e

set_option maxHeartbeats 1000000 in

theorem natActR_VtupR (R : Type) [Field R] (g : ∀ v, Fin (P.n' v) → GL (Fin (P.m + 1)) R) (Q : XR P R)
    (hQ : Q ∈ VtupR P R) : natActR P R g Q ∈ VtupR P R := by
  unfold VtupR at hQ ⊢
  induction hQ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨F, hF, rfl⟩ := hx
    apply Submodule.subset_span
    refine ⟨fun v => Formalism.MainNotions.G.LatticeSystems.je_rho R (P.lam0 v) (fun s => (g v s : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) R)) (F v),
      fun v => Formalism.MainNotions.G.LatticeSystems.je_V R (P.lam0 v) _ (F v) (hF v), ?_⟩
    unfold natActR
    rw [LinearMap.smul_apply, AlgHom.toLinearMap_apply, map_prod]
    simp only [substR_rename]
    rw [Finset.prod_congr rfl (fun v _ => (Finset.prod_congr rfl fun s _ => rfl :
      ∏ s : Fin (P.n' v), (g v s : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) R).det ^ (-(eAt P v s)) =
        ∏ s : Fin (P.n' v), (g v s : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) R).det ^ (-(eAt P v s))))]
    rw [Formalism.MainNotions.G.LatticeSystems.je_prod_smul]
    refine Finset.prod_congr rfl fun v _ => ?_
    have hb : (fun s => (((g v s)⁻¹ : GL (Fin (P.m + 1)) R) : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) R)) =
        fun s => ((g v s : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) R))⁻¹ :=
      funext fun s => Matrix.coe_units_inv (g v s)
    have e2 : Formalism.MainNotions.G.LatticeSystems.je_rho R (P.lam0 v) (fun s => (g v s : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) R)) (F v) =
        (∏ s : Fin (P.n' v), (g v s : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) R).det ^ (-(eAt P v s))) •
          Formalism.GradedWeylDivisibility.blockAct R (fun s => (((g v s)⁻¹ : GL (Fin (P.m + 1)) R) : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) R)) (F v) := by
      rw [hb]
      rfl
    rw [e2, map_smul]
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx

end Stab

theorem vtupStab (tE : Tau → E →+* LL) : VtupStab G A pos tE (σ := σ) (J := J) :=
  fun _ _ Q hQ => natActR_VtupR G.P LL _ Q hQ

theorem evRatPt_of (tE : Tau → E →+* LL) (htE : ∀ τ x, embLL (tE τ x) = emb τ x)
    (hBs : cT (σ : E →+* E) A.B.1 * J * A.B.1 = 1) (h1 : EvRatRep emb embLL G A pos embV)
    (h2 : ChiRatAll S embLL) (h3 : VtupStab G A pos tE (σ := σ) (J := J)) : EvRatPt S emb embLL G A pos embV := by
  intro x c γ hγ κ
  obtain ⟨Qc, hQcV, hQc⟩ := h1 x c
  obtain ⟨r, hr⟩ := h2 κ
  refine ⟨r • natActR G.P LL (blkLL A σ tE pos γ) Qc, Submodule.smul_mem _ r (h3 γ hγ Qc hQcV), fun z z' hz => ?_⟩
  have hb := evC_blk A tE pos emb embLL htE γ (unit_of_std A.B γ hBs hγ) (gramC J emb) z' z hz Qc
  rw [map_smul' embLL r, map_smul, Pi.smul_apply, hb, hQc, hr, smul_eq_mul]

theorem valEx_of_rep (tE : Tau → E →+* LL) (htE : ∀ τ x, embLL (tE τ x) = emb τ x)
    (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x)) (hBs : cT (σ : E →+* E) A.B.1 * J * A.B.1 = 1) (hA : AdExt S emb embLL embV yc) (hP : PtEx S G A yc)
    (hO : PtOne S G A) (h1 : EvRatRep emb embLL G A pos embV) (h2 : ChiRatAll S embLL) (h3 : VtupStab G A pos tE (σ := σ) (J := J)) :
    ValEx S emb embLL G A pos embV yc :=
  valEx_of' hc hA hP hO (evRatPt_of tE htE hBs h1 h2 h3)

theorem valEx_of_rep' (tE : Tau → E →+* LL) (htE : ∀ τ x, embLL (tE τ x) = emb τ x)
    (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x)) (hBs : cT (σ : E →+* E) A.B.1 * J * A.B.1 = 1) (hA : AdExt S emb embLL embV yc) (hP : PtEx S G A yc)
    (hO : PtOne S G A) (h1 : EvRatRep emb embLL G A pos embV) (h2 : ChiRatAll S embLL) :
    ValEx S emb embLL G A pos embV yc :=
  valEx_of_rep tE htE hc hBs hA hP hO h1 h2 (vtupStab tE)

end Formalism.L2.G.Cmp
