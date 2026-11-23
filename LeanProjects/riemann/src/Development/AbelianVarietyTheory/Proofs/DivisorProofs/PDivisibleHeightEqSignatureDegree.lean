import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaSuccPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvEqOneOfForallPairing
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelLabelExtendsOfOrthogonalToExtended

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.PDiv GlobalTheory.PDivGroup WithConv
open GlobalTheory.DeRham (spOver spOver_comp)

open GlobalTheory GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Closed

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GroupBplus.Closed

theorem height_eq_lattice_rank : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {t : SAB H (Sp k)} {p : ℕ} [Fact p.Prime] {GG : PDivGroup p k} (tw : GG.TorsionTower t.G) (I : GeomTate Dw t), GG.height = 2 * (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) := by
  intro E _ _ _ H Dw k _ _ _ t p _ GG tw I
  obtain ⟨hfr, hfi, hrk⟩ := GlobalTheory.Coisotropic.lattice_rank E H Dw
  have hp : 0 < p ^ 1 := pow_pos (Fact.out : p.Prime).pos 1
  let g : Dw.La →+ Additive (SpAlg k k ⟶ t.G) :=
    AddMonoidHom.mk' (fun x => Additive.ofMul (selfIso.hom ≫ I.ev (p ^ 1) x)) fun x y => by
      rw [I.add, MonObj.comp_mul, ofMul_mul]
  have hker : g.ker = (nsmulAddMonoidHom (p ^ 1) : Dw.La →+ Dw.La).range := by
    ext x
    have h1 : g x = 0 ↔ I.ev (p ^ 1) x = 1 := by
      change selfIso.hom ≫ I.ev (p ^ 1) x = 1 ↔ _
      rw [← MonObj.comp_one selfIso.hom, cancel_epi]
    rw [AddMonoidHom.mem_ker, h1, I.ker _ hp]
    exact ⟨fun ⟨b, hb⟩ => ⟨b, hb.symm⟩, fun ⟨b, hb⟩ => ⟨b, hb.symm⟩⟩
  have hcard : Nat.card (GG.A 1 →ₐ[k] k) = Nat.card g.range := by
    refine Nat.card_eq_of_bijective (fun φ => ⟨Additive.ofMul (spOver φ ≫ tw.y 1), ?_⟩) ⟨?_, ?_⟩
    · have h := (tw.exists_iff 1 (spOver φ ≫ tw.y 1)).1 ⟨φ, rfl⟩
      obtain ⟨a, ha⟩ := (I.onto _ hp (selfIso.inv ≫ spOver φ ≫ tw.y 1)).1 (by
        rw [← MonObj.comp_pow, h, MonObj.comp_one])
      refine ⟨a, congrArg Additive.ofMul ?_⟩
      rw [ha, Iso.hom_inv_id_assoc]
    · intro φ ψ h
      exact tw.inj 1 k _ _ (Additive.ofMul.injective (congrArg Subtype.val h))
    · rintro ⟨_, a, rfl⟩
      exact ⟨latPt tw I 1 a, Subtype.ext (congrArg Additive.ofMul (latPt_y tw I 1 a))⟩
  rw [GG.natCard_pts_eq k 1, ← AddSubgroup.index_ker, hker, AddSubgroup.index_range_nsmul, hrk,
    pow_one, _root_.one_mul] at hcard
  exact Nat.pow_right_injective (Fact.out : p.Prime).two_le hcard

end GlobalTheory.GroupBplus.Closed
