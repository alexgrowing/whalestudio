import Formalism.LocalToGlobal.HermitianForms.PrkSmul
import Formalism.LocalToGlobal.HermitianForms.Transport
import Formalism.LocalToGlobal.HermitianForms.FramesLemmas

namespace Formalism.L2.Forms

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

variable {D : D7} {u : D.what₂.Word} {A : AtTTied u} {i : ℕ} {hi : i ≤ D.R.m}

set_option maxHeartbeats 4000000 in
theorem UpTie.explicit {P : LvTied u A i hi} {K : ClsTied u i hi} {W : ValTied u A.eV i hi K} (h : UpTie P K W)
    (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) (z : ↥(Ld D u i hi c)) (hz : (D.fm u).fv i v c (P.pr v c z) = 1) :
    ∃ (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi)) (κ : K.lev.U), ∀ g ∈ AdFun K.lev (embT D), ∀ s s',
      IsTr (atInf (embT D) γ.1.1) (W.eY s') (W.eY s) →
      (D.fm u).upT i v c (P.pr v c z) (fun s => g (K.y ((D.fm u).up i v c (P.pr v c z))) (W.eY s)) s =
        (((K.lev.chi κ)⁻¹ : ℂˣ) : ℂ) * g (K.y ((D.fm u).up i v c (P.pr v c z))) (W.eY s') := by
  obtain ⟨γ, η, κ, _, heq, _, _, _, htr⟩ := h v c z hz
  refine ⟨γ, κ, fun g hg s s' hs => ?_⟩
  rw [htr g hg]
  exact AdFun_transport K.lev (embT D) g hg γ.1 γ.2 (K.y c * η) _ κ heq _ _ hs

set_option maxHeartbeats 4000000 in
theorem DnTie.explicit {P : LvTied u A i hi} {K : ClsTied u i hi} {W : ValTied u A.eV i hi K} (h : DnTie P K W)
    (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk i v c)) (hg0 : g ≠ 0) :
    ∃ (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi)) (κ : K.lev.U), ∀ f ∈ AdFun K.lev (embT D), ∀ s s',
      IsTr (atInf (embT D) γ.1.1) (W.eY s') (W.eY s) →
      (D.fm u).dnT i v c g (fun s => f (K.y ((D.fm u).dn i v c g)) (W.eY s)) s =
        (((K.lev.chi κ)⁻¹ : ℂˣ) : ℂ) * f (K.y ((D.fm u).dn i v c g)) (W.eY s') := by
  obtain ⟨γ, η, κ, _, heq, _, _, htr⟩ := h v c g hg0
  refine ⟨γ, κ, fun f hf s s' hs => ?_⟩
  rw [htr f hf]
  exact AdFun_transport K.lev (embT D) f hf γ.1 γ.2 (K.y c * η) _ κ heq _ _ hs

set_option maxHeartbeats 4000000 in

theorem UpNatTie.upTie {P : LvTied u A i hi} {K : ClsTied u i hi} {W : ValTied u A.eV i hi K} (h : UpNatTie P K W) :
    UpTie P K W := by
  intro v c z hz
  obtain ⟨γ, η, κ, h1, h2, h3, h4, h5, h6⟩ := h v c z hz
  refine ⟨γ, η, κ, h1, h2, h3, h4, h5, fun g hg => ?_⟩
  funext s
  obtain ⟨y', hy'⟩ := exists_isTr' (embT D) γ.1 (W.eY s)
  have hs : IsTr (atInf (embT D) γ.1.1) (W.eY (W.eY.symm y')) (W.eY s) := by
    rw [Equiv.apply_symm_apply]; exact hy'
  rw [h6 _ s _ hs]
  exact (AdFun_transport K.lev (embT D) g hg γ.1 γ.2 (K.y c * η) _ κ h2 _ _ hs).symm

set_option maxHeartbeats 4000000 in

theorem DnNatTie.dnTie {P : LvTied u A i hi} {K : ClsTied u i hi} {W : ValTied u A.eV i hi K} (h : DnNatTie P K W) :
    DnTie P K W := by
  intro v c g hg0
  obtain ⟨γ, η, κ, h1, h2, h3, h4, h5⟩ := h v c g hg0
  refine ⟨γ, η, κ, h1, h2, h3, h4, fun f hf => ?_⟩
  funext s
  obtain ⟨y', hy'⟩ := exists_isTr' (embT D) γ.1 (W.eY s)
  have hs : IsTr (atInf (embT D) γ.1.1) (W.eY (W.eY.symm y')) (W.eY s) := by
    rw [Equiv.apply_symm_apply]; exact hy'
  rw [h5 _ s _ hs]
  exact (AdFun_transport K.lev (embT D) f hf γ.1 γ.2 (K.y c * η) _ κ h2 _ _ hs).symm

end Formalism.L2.Forms
