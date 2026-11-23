import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsPtMoveEq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ReindexRenamePointDetLatK
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.EqOneOfPh
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.Xc.Mv0

theorem frm_gen {E Q : Type} [Field E] [Field Q] (σ : E →+* E) {a N : ℕ} (rk hr : a = N) (J0 : Matrix (Fin N) (Fin N) E)
    (B g : GL (Fin N) E) (iw : E →+* Q) (M : GL (Fin a) Q) (hM : castGL rk Q M = bc iw (B⁻¹ * g * B)) :
    (((LinearMap.toMatrix' ((stdCo σ (J0.reindex (finCongr rk.symm) (finCongr rk.symm)) : (Fin a → E) ≃ₗ[E] (Fin a → E)) :
      (Fin a → E) →ₗ[E] (Fin a → E))) * ((reGL (finCongr rk.symm) B : GL (Fin a) E) : Matrix (Fin a) (Fin a) E)).map iw).submatrix
        (finCongr (rfl : a = a)) (finCongr (rfl : a = a)) * (M : Matrix (Fin a) (Fin a) Q) =
    (eMat hr σ J0 g).map iw *
      ((((LinearMap.toMatrix' ((stdCo σ (J0.reindex (finCongr rk.symm) (finCongr rk.symm)) : (Fin a → E) ≃ₗ[E] (Fin a → E)) :
      (Fin a → E) →ₗ[E] (Fin a → E))) * ((reGL (finCongr rk.symm) B : GL (Fin a) E) : Matrix (Fin a) (Fin a) E)).map iw).submatrix
        (finCongr (rfl : a = a)) (finCongr (rfl : a = a))) := by
  subst rk
  have hJ : J0.reindex (finCongr (rfl : a = a)) (finCongr (rfl : a = a)) = J0 := by ext i j; simp
  have hB : ((reGL (finCongr (rfl : a = a)) B : GL (Fin a) E) : Matrix (Fin a) (Fin a) E) = (B : Matrix (Fin a) (Fin a) E) := by
    ext i j
    show (Matrix.reindexAlgEquiv E E (finCongr (rfl : a = a)) (B : Matrix (Fin a) (Fin a) E)) i j = _
    simp [Matrix.reindexAlgEquiv_apply]
  have hMm : (M : Matrix (Fin a) (Fin a) Q) = ((B⁻¹ * g * B : GL (Fin a) E) : Matrix (Fin a) (Fin a) E).map iw := by
    ext i j
    have h1 := congrArg (fun x : GL (Fin a) Q => (x : Matrix (Fin a) (Fin a) Q) i j) hM
    simp only [castGL_apply] at h1
    exact h1
  have hE : eMat hr σ J0 g = LinearMap.toMatrix' ((stdCo σ J0 : (Fin a → E) ≃ₗ[E] (Fin a → E)) : (Fin a → E) →ₗ[E] (Fin a → E)) *
      (g : Matrix (Fin a) (Fin a) E) *
      LinearMap.toMatrix' (((stdCo σ J0).symm : (Fin a → E) ≃ₗ[E] (Fin a → E)) : (Fin a → E) →ₗ[E] (Fin a → E)) := by
    have e0 : eMat hr σ J0 g = LinearMap.toMatrix' (stdG σ J0 g).toLinearMap := by ext i j; simp [eMat]
    rw [e0]
    have e1 : (stdG σ J0 g).toLinearMap = (stdCo σ J0 : (Fin a → E) →ₗ[E] (Fin a → E)) ∘ₗ (Matrix.toLin' (g : Matrix (Fin a) (Fin a) E)) ∘ₗ
        ((stdCo σ J0).symm : (Fin a → E) →ₗ[E] (Fin a → E)) := by
      apply LinearMap.ext; intro x; rfl
    rw [e1, LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', Matrix.mul_assoc]
  have hsub : ∀ A : Matrix (Fin a) (Fin a) Q, A.submatrix (finCongr (rfl : a = a)) (finCongr (rfl : a = a)) = A := fun A => by ext i j; rfl
  rw [hsub, hJ, hB, hMm, hE, ← Matrix.map_mul, ← Matrix.map_mul]
  congr 1
  have hci : LinearMap.toMatrix' (((stdCo σ J0).symm : (Fin a → E) ≃ₗ[E] (Fin a → E)) : (Fin a → E) →ₗ[E] (Fin a → E)) *
      LinearMap.toMatrix' ((stdCo σ J0 : (Fin a → E) ≃ₗ[E] (Fin a → E)) : (Fin a → E) →ₗ[E] (Fin a → E)) = 1 := by
    rw [← LinearMap.toMatrix'_comp, LinearEquiv.symm_comp, LinearMap.toMatrix'_id]
  have hBB : (B : Matrix (Fin a) (Fin a) E) * ((B⁻¹ : GL (Fin a) E) : Matrix (Fin a) (Fin a) E) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  simp only [Units.val_mul]
  calc _ = LinearMap.toMatrix' ((stdCo σ J0 : (Fin a → E) ≃ₗ[E] (Fin a → E)) : (Fin a → E) →ₗ[E] (Fin a → E)) *
        ((B : Matrix (Fin a) (Fin a) E) * ((B⁻¹ : GL (Fin a) E) : Matrix (Fin a) (Fin a) E)) * (g : Matrix (Fin a) (Fin a) E) * (B : Matrix (Fin a) (Fin a) E) := by
          simp only [Matrix.mul_assoc]
    _ = _ := by
          rw [hBB, Matrix.mul_one]
          calc _ = LinearMap.toMatrix' ((stdCo σ J0 : (Fin a → E) ≃ₗ[E] (Fin a → E)) : (Fin a → E) →ₗ[E] (Fin a → E)) * (g : Matrix (Fin a) (Fin a) E) *
                (LinearMap.toMatrix' (((stdCo σ J0).symm : (Fin a → E) ≃ₗ[E] (Fin a → E)) : (Fin a → E) →ₗ[E] (Fin a → E)) *
                  LinearMap.toMatrix' ((stdCo σ J0 : (Fin a → E) ≃ₗ[E] (Fin a → E)) : (Fin a → E) →ₗ[E] (Fin a → E))) * (B : Matrix (Fin a) (Fin a) E) := by
                rw [hci, Matrix.mul_one]
            _ = _ := by simp only [Matrix.mul_assoc]

end GlobalTheory.TwV.Xc.Mv0

namespace GlobalTheory.TwV.Xc.Mv0

open Formalism.MainNotions.G.CmpJ.PStabEq

theorem regl2 {R : Type} [CommRing R] {a N : ℕ} (h : a = N) (h' : N = a) (y : GL (Fin N) R) :
    Formalism.L2.PairingIndexBounds.F.reGL (finCongr h) (Formalism.L2.PairingIndexBounds.F.reGL (finCongr h') y) = y := by
  subst h
  ext i j
  show (Matrix.reindexAlgEquiv R R (finCongr (rfl : a = a)) (Matrix.reindexAlgEquiv R R (finCongr h') (y : Matrix (Fin a) (Fin a) R))) i j = _
  simp [Matrix.reindexAlgEquiv_apply]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n p : ℕ} {G : GAtP p}
  {A : LocAt F E n G} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))} {S : StepLevel F E σ J T f bad}
  {cl : Type} {y : cl → UPts σ J (FiniteAdeleRing (𝓞 F) F)}

theorem ptEps_spec (H1 : OneHyp S A y) (i : G.comp) (g : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v)) :
    A.IsPt i g (Classical.epsilon fun x => A.IsPt i g x ∧ x ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F)) ∧
      (Classical.epsilon fun x => A.IsPt i g x ∧ x ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F)) ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) := by
  obtain ⟨c, γ₀, κ₀, hγ₀, hp⟩ := ptEx_of H1.good S y H1.y_bij.2 i g
  exact Classical.epsilon_spec (p := fun x => A.IsPt i g x ∧ x ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F))
    ⟨_, hp, Subgroup.mul_mem _ (Subgroup.mul_mem _ (bc_mem hγ₀) (y c).2) (U_le κ₀.2)⟩

theorem pt_gen (H1 : OneHyp S A y) (i : G.comp) (γ : (G.lev i).Γ) (L : G.P.Tup) (hL : G.P.IsLatTup L) (κa : S.U)
    (hκa : A.IsAway i γ κa.1) (bas : G.P.Tup → ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v))
    (hbas : ∀ L' v, bas L' v = Classical.epsilon fun g : GL (Fin (G.P.m + 1)) (G.P.Qq v) =>
      L' v = colSpan (G.P.W v) (g : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v))) :
    ∃ κ : S.U, (Classical.epsilon fun x => A.IsPt i (bas ((G.lev i).smul γ L)) x ∧ x ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F)) =
      GlobalTheory.TwU.ratA F (A.gamI i γ) * (Classical.epsilon fun x => A.IsPt i (bas L) x ∧ x ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F)) * κ.1 ∧
      S.chi κ * S.chi κa = 1 := by
  obtain ⟨g0, hg0⟩ := exists_bases1 L hL
  have hb : ∀ (L' : G.P.Tup) (g1 : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v)),
      (∀ v, L' v = colSpan (G.P.W v) (g1 v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v))) →
      ∀ v, L' v = colSpan (G.P.W v) (bas L' v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)) := by
    intro L' g1 h v
    rw [hbas]
    exact Classical.epsilon_spec (p := fun g : GL (Fin (G.P.m + 1)) (G.P.Qq v) =>
      L' v = colSpan (G.P.W v) (g : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v))) ⟨g1 v, h v⟩
  have hbL := hb L g0 hg0
  have hbγ := hb _ _ (smul_colSpan i γ L g0 hg0)
  have hs := ptEps_spec H1 i (bas L)
  have hs' := ptEps_spec H1 i (bas ((G.lev i).smul γ L))
  exact GlobalTheory.TwV.Xc.isPt_move_eq F E σ n p G A J T f bad S H1.good H1.int H1.hypP H1.actB H1.bad_p i γ (H1.gamU i γ) κa hκa
    (bas L) (bas ((G.lev i).smul γ L)) (fun v => (hbγ v).symm.trans (smul_colSpan i γ L (bas L) hbL v))
    ⟨_, hs.2⟩ ⟨_, hs'.2⟩ hs.1 hs'.1

end GlobalTheory.TwV.Xc.Mv0

namespace GlobalTheory.TwV.Xc

set_option maxHeartbeats 4000000 in

theorem moveBy_zero : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ (c : (sysS H X std).Lv.comp 0) (La : ((sysS H X std).Pj 0).Tup) (γ : ((sysS H X std).Lv.lev 0 c).Γ), ((sysS H X std).Pj 0).IsLatTup La → ∃ g κ, MoveBy std J 0 (Nat.zero_le _) c La γ g κ) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X _ std t J S hD hS c La γ hL
  have hfr : ∀ (hr : ((sysS H X std).Pj 0).m + 1 = D.R.N 0) (v : (sysS H X std).Pl),
      (J.fd std).frM 0 (c, La) v * (gamAt (sysS H X std) 0 c γ v : Matrix _ _ _) =
        (eMat hr (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)) ((A0 J).gamI c γ)).map (J.rho std v) * (J.fd std).frM 0 (c, La) v := by
    intro hr v
    exact Mv0.frm_gen _ (A0 J).rk hr (gramN D 0 (Nat.zero_le _)) (A0 J).B ((A0 J).gamI c γ) ((A0 J).iw v) _ (J.one.actB c v γ)
  obtain ⟨κa, hκa⟩ := awayEx_of J.one.good _ J.one.gam c γ
  obtain ⟨ra, hra1, hra2⟩ := (lev0AtOf_compatible J.Gd.cmp u w hg).chi c γ κa hκa
  have hJpt : ∀ L', (J.pt std 0 (Nat.zero_le _) (c, L')).1 = Classical.epsilon fun x => (A0 J).IsPt c (basesAt _ std _ _ _ _ _ _ _ 0 L') x ∧
      x ∈ UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := by
    intro L'
    have hs := Mv0.ptEps_spec J.one c (basesAt _ std _ _ _ _ _ _ _ 0 L')
    have hspec : J.IsPt std 0 (Nat.zero_le _) (c, L') (J.pt std 0 (Nat.zero_le _) (c, L')) :=
      Classical.epsilon_spec (p := J.IsPt std 0 (Nat.zero_le _) (c, L')) ⟨⟨_, hs.2⟩, (A0 J).rk, (Mv0.regl2 _ _ _).symm⟩
    obtain ⟨hr, e⟩ := hspec
    rw [e]
    exact Mv0.regl2 _ _ _
  obtain ⟨κ, hκ1, hκ2⟩ := Mv0.pt_gen J.one c γ La hL κa hκa (basesAt _ std _ _ _ _ _ _ _ 0) (fun L' v => rfl)
  obtain ⟨-, -, hU, hchi⟩ := J.lev0 (J.chart std 0 (Nat.zero_le _) (c, La))
  have hmem : κ.1 ∈ ((J.St 0 (Nat.zero_le _)).K (J.chart std 0 (Nat.zero_le _) (c, La))).lev.U := by rw [hU]; exact κ.2
  refine ⟨(A0 J).gamI c γ, ⟨κ.1, hmem⟩, J.one.gamU c γ, ?_, hfr, ra⁻¹, ?_, ?_⟩
  · exact (hJpt _).trans (hκ1.trans (by rw [hJpt]))
  · rw [hchi ⟨κ.1, hmem⟩ κ rfl, map_inv₀, hra1, ← Units.val_inv_eq_inv_val]
    exact congrArg (fun z : ℂˣ => (z : ℂ)) (eq_inv_of_mul_eq_one_left hκ2).symm
  · rw [map_inv₀]
    exact eq_inv_of_mul_eq_one_left hra2

end GlobalTheory.TwV.Xc

end
