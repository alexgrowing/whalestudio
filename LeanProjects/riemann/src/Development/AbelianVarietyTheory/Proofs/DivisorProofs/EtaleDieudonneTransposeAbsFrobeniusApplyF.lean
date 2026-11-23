import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRedDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DieudonneFunctorBaseFunctorProperties

set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.Dieu.EtFromConn

namespace GlobalTheory.Dieu.EtFromConn

theorem isTr_absFrob_F : ∀ (p : ℕ) [Fact p.Prime] (B : Base p (fun _ _ G => G.IsConn)) (k : Type)
    [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k) (h : G.IsEt) (l l' : Mod B G h),
    IsTr B (frobRing (p_eq_zero p k)) h h (absFrob (p_eq_zero p k) G) l l' →
      ∀ y, l' (B.F G.dual (dual_conn h) y) = p * WittVector.frobenius (l y) := by
  intro p _ B k _ _ _ G h l l' hT y
  set hp := p_eq_zero p k
  letI : Algebra k k := (frobRing hp).toAlgebra
  obtain ⟨hb, lb, h1, h2⟩ := hT
  have hd := dual_conn h

  have eV : (PerfdLat.dualBaseChange k G).inv ≫ dualHom G (G.baseChange k)
      (absFrob hp G).lift = verschiebung hp G.dual := by
    have := dualHom_relFrob hp G
    change (frobTwistDual hp G).inv ≫ dualHom G _ (relFrob hp G) = _
    rw [← this, Iso.inv_hom_id_assoc]

  have eF : B.F G.dual hd y = B.map hd hb (relFrob hp G.dual)
      (B.smap hb hd (G.dual.toBase k) y) := by
    change B.smap hd hd (absFrob hp G.dual) y = B.smap hd hb (SemiHom.ofHom (relFrob hp G.dual))
      (B.smap hb hd (frobProj hp G.dual) y)
    exact B.smap_comp hd hb hd (frobProj hp G.dual) (SemiHom.ofHom (relFrob hp G.dual))
      (absFrob hp G.dual) (fun n a => by
        change (absFrob hp G.dual).app n a = (relFrob hp G.dual).app n ((frobProj hp G.dual).app n a)
        exact ((relFrob_app_frobProj hp n a).trans (absFrob_app hp G.dual n a).symm).symm) y
  have P := base_functor_props p _ B k (frobTwist hp G.dual) G.dual (frobTwist hp G.dual) hb hd hb
  have P' := base_functor_props p _ B k (frobTwist hp G.dual) (frobTwist hp G.dual)
    (frobTwist hp G.dual) hb hb hb
  have ep : B.map hb hd (verschiebung hp G.dual) (B.map hd hb (relFrob hp G.dual)
      (B.smap hb hd (G.dual.toBase k) y)) = p ^ 1 • B.smap hb hd (G.dual.toBase k) y := by
    set x := B.smap hb hd (G.dual.toBase k) y
    have c := P.2.1 (verschiebung hp G.dual) (relFrob hp G.dual)
    rw [verschiebung_comp_relFrob] at c
    have c2 := LinearMap.congr_fun c x
    calc B.map hb hd (verschiebung hp G.dual) (B.map hd hb (relFrob hp G.dual) x)
        = B.map hb hb ((p : ℤ_[p]) • 𝟙 _) x := c2.symm
      _ = p ^ 1 • B.map hb hb (𝟙 (frobTwist hp G.dual)) x := by
          have e := P'.2.2.2.2.1 1 (𝟙 (frobTwist hp G.dual)) x
          simp only [pow_one] at e ⊢
          exact e
      _ = p ^ 1 • x := congrArg _ (LinearMap.congr_fun P'.1 x)
  rw [h2, eV, eF, ep, map_nsmul, h1, nsmul_eq_mul, pow_one]
  congr 1
  rw [WittVector.frobenius_eq_map_frobenius]
  congr 2
  exact RingHom.ext fun r => frobRing_apply hp r

end GlobalTheory.Dieu.EtFromConn
