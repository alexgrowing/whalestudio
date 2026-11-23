import Formalism.LocalToGlobal.Columns.CoordLatticeSelfDualAuxiliary

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem hs_padL_succ (n : ℕ) : padL E n (n + 1) = incl E n := by
  apply LinearMap.ext
  intro x
  funext j
  rw [padL_apply]
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp [incl]
  · simp [incl]

theorem hs_extUH_pad {N n : ℕ} (hN : N = n + 1) (g : UF E n) (x : Fin n → E) :
    (extUH hN g).1 (padL E n N x) = padL E n N (g.1 x) := by
  subst hN
  rw [hs_padL_succ]
  show extE g.1 (incl E n x) = incl E n (g.1 x)
  apply sp_ext
  · rw [initL_extE, initL_incl, initL_incl]
  · rw [extE_last]
    simp [incl]

theorem hs_extUH_last {N n : ℕ} (hN : N = n + 1) [NeZero N] (g : UF E n) (p : E) :
    (extUH hN g).1 (Pi.single (lastIdx N) p) = Pi.single (lastIdx N) p := by
  subst hN
  rw [← lastVector_eq_single]
  show extE g.1 (z0 E n p) = z0 E n p
  apply sp_ext
  · rw [initL_extE]
    simp [z0]
  · rw [extE_last]

theorem hs_conj {N : ℕ} (g e : UF E N) (w : Sp E N) : g.1 ((g⁻¹ * e * g⁻¹⁻¹).1 (g.1.symm w)) = e.1 w := by
  rw [inv_inv]
  show g.1 (g.1.symm (e.1 (g.1 (g.1.symm w)))) = e.1 w
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

theorem hs_core {V V' : Type} [AddCommGroup V] [Module E V] [AddCommGroup V'] [Module E V'] {N n : ℕ} (hN : N = n + 1) [NeZero N]
    (e : V ≃ₗ[E] (Fin N → E)) (e' : V' ≃ₗ[E] (Fin n → E)) (ι : V' →ₗ[E] V) (hι : ∀ x, e (ι x) = padL E n N (e' x))
    (γ M : V ≃ₗ[E] V) (S : V' ≃ₗ[E] V') (g₀ : UF E N) (s : UF E n)
    (hγ : ∀ x, e (γ x) = g₀.1 (e x)) (hM : ∀ x, e (M x) = (g₀⁻¹ * extUH hN s * g₀⁻¹⁻¹).1 (e x)) (hSs : ∀ x, e' (S x) = s.1 (e' x))
    (z : V) (p : E) (hz : e z = Pi.single (lastIdx N) p) :
    (∀ x, γ (M (γ.symm (ι x))) = ι (S x)) ∧ γ (M (γ.symm z)) = z := by
  have hγs : ∀ y, e (γ.symm y) = g₀.1.symm (e y) := fun y => by
    rw [LinearEquiv.eq_symm_apply, ← hγ, LinearEquiv.apply_symm_apply]
  constructor
  · intro x
    apply e.injective
    rw [hγ, hM, hγs, hs_conj, hι, hs_extUH_pad, hι, hSs]
  · apply e.injective
    rw [hγ, hM, hγs, hs_conj, hz, hs_extUH_last]

variable {F : Type} [Field F] [NumberField F] [Algebra F E]

theorem hs_stab_crd (hc : CMData F E) {V : Type} [AddCommGroup V] [Module E V] {n' n : ℕ} [NeZero n] (b : Basis (Fin n') E V) (h : n' = n)
    (g : GL (Fin n') E) (t : UF E n) (hg : Formalism.L2.Forms.reGL h E g = ((ratEquiv hc n).symm t).1) (x : V) :
    hqCrd b h ((Formalism.L2.Herm.toGLb b).symm g x) = t.1 (hqCrd b h x) := by
  have h1 := hq_reGL_mulVec b h ((Formalism.L2.Herm.toGLb b).symm g) x
  rw [MulEquiv.apply_symm_apply, hg, ← rlc_ratHom_apply hc n] at h1
  have h2 : ratHom hc n ((ratEquiv hc n).symm t) = t := (ratEquiv hc n).apply_symm_apply t
  rw [h2] at h1
  exact h1.symm

end Gen

section GenL

variable {X : Fields} {Pr : Primes X} (hc : CMData X.F X.E) (hX : X.Ok) (hPr : Pr.Ok) (σ₀ : X.K →+* ℂ) (u : Pr.Word)
  {n : ℕ} [NeZero n] (Λ : LevFam X.E X.K n Pr.vGs)
  (c₀ : DiaG X.E (Pr.vT u)) (s : DecoCl n (Pr.vT u) Pr.vGs Λ.grp → DecoSet X.E n (Pr.vT u) Pr.vGs)

theorem levPack_stabI (hS : DecoPtSurj hc n (Pr.vT u) Pr.vGs) (hs : ∀ c, decoCls n (Pr.vT u) Pr.vGs Λ.grp (s c) = c)
    (hK : LocalLevelIsKOneAtT hc u Λ) (H : HCrd Pr n fun c => (s c).1.L) (c : DecoCl n (Pr.vT u) Pr.vGs Λ.grp)
    (t : MulAction.stabilizer (UF X.E n × Λ.grp) (s c)) :
    Formalism.L2.Forms.reGL H.hn X.E ((levPack hc hX hPr σ₀ u Λ c₀ s hS hs hK H).cls.stabI c t).1 = ((ratEquiv hc n).symm t.1.1).1 := by
  obtain ⟨n', hn, J, rfl, f, rfl, bad, rfl, lat, hlat⟩ := H
  subst hn
  obtain rfl : lat = fun c => (s c).1.L := funext fun c => (hlat c).trans (Formalism.L2.Forms.reL_rfl _)
  exact Formalism.L2.Forms.reGL_rfl _ _

end GenL

section Rec

variable {d : ColDat} (a : ColArgs d) (hS : SpStd d.toColBase) (hH : HostHyp d) (hP : PtSurjP d) (hQ : PtSurj d) (hK : LocalLevelIsKOneEverywhere d)
  (S : GSplit (Pr := d.Pr) d.sp.cm) (hI : IwAll d S)

include hS in

theorem hs_iX (x : d.sp.X'.V) :
    CF.crdN (d.colRec a) d.R.m le_rfl (d.sp.iX' x) = padL d.host.E (d.R.N d.R.m - 1) (d.R.N d.R.m) (CF.crdP (d.colRec a) x) := by
  rw [← iXc_eq a hS]
  show _ = CF.crdN (d.colRec a) d.R.m le_rfl (d.sp.iX' ((CF.crdP (d.colRec a)).symm (CF.crdP (d.colRec a) x)))
  rw [LinearEquiv.symm_apply_apply]

theorem hs_tilG (u : d.what₂.Word) (c : PCl d) (x : (d.sp.X d.R.m).V) :
    CF.crdN (d.colRec a) d.R.m le_rfl (((levelExponentAtT a hS hH hP u).tilG c).1 x) =
      (d.tilMv u c).1.1 (CF.crdN (d.colRec a) d.R.m le_rfl x) :=
  (hqG_crd d.R.m le_rfl ((tildeLatticeAgreement a hS hH hP u).ga c) x).trans (tilGa_mulVec u c _)

set_option maxHeartbeats 4000000 in

theorem stabMapTied (disc : ∀ u, AtTDisc (d.colRec a) u)
    (moves : ∀ u, AtTMoves (atTTied a hH u) (fun i hi => levelAgreement a hS hH u i hi)) :
    CH.StabMapTied (d.colRec a) (hermCols a hS hQ hK S hI) (hermAtT a hS hH ⟨disc, moves, levelExponentAtT a hS hH hP⟩) := by
  intro u h1 c s
  exact hs_core (E := d.X.E) (N_m_succ d.R) (CF.crdN (d.colRec a) d.R.m le_rfl) (CF.crdP (d.colRec a)) d.sp.iX' (hs_iX a hS)
    ((levelExponentAtT a hS hH hP u).tilG c).1 _ _ (d.tilMv u c).1 s.1.1 (hs_tilG a hS hH hP u c)
    (fun x => hs_stab_crd d.sp.cm (d.sp.X d.R.m).frame (CF.rankN (d.colRec a) d.R.m le_rfl) _ _
      (levPack_stabI d.sp.cm d.hX d.hPr d.σ₀ u (d.lev d.R.m) _ _ _ _ (hK u d.R.m) (hCrd hS u d.R.m le_rfl) _
        (stabMapR (Pr := d.Pr) (W := d.W) (Λ := d.lev) (Finset.Subset.refl _) (ΛM := d.levP) d.hPr u (a.piT_off u) a.levExt c s)) x)
    (fun x => hs_stab_crd d.sp.cm d.sp.X'.frame (CF.rankP (d.colRec a)) _ _
      (levelPacking_stabilizer d.sp.cm d.hPr d.σ₀ d.levP.inv d.reprP hP _ (hCrdP a hS hH hP u) c s) x)
    (levelExponentAtT a hS hH hP u).z0 (d.piT u : d.host.E) (joint_lastVector a hS hH hP u).symm

end Rec

end Formalism.L2.Col
