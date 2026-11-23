import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRepFam
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisCoverQuotientFreeFiniteAction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQProjOverTargetGaloisCoverNoetherian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQProjOverOfRelAmpleOverQprojNoetherian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDescendsGaloisCoverNoetherianBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullClsDiag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareBundleDescentGaloisCover
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GaloisCoverDescentAndCartesianSquares
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorObjectMapsComposeCancel

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT.MapUniq

open GlobalTheory.UPel.HT.MapComp

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}

theorem exists_auto {S S' : Scheme.{0}} {s : S ⟶ Sp R} {s' : S' ⟶ Sp R} {o' : Obj b N s'} {o : Obj b N s}
    {f : S' ⟶ S} (m m' : ObjMap o' o f) : ∃ a : ObjMap o' o' (𝟙 S'), a.φ ≫ m'.φ = m.φ := by
  have w : m.φ ≫ o.A.hom = o'.A.hom ≫ f := m.cart.1.w
  set ψ := m'.cart.1.lift m.φ o'.A.hom w
  have hψ : ψ ≫ m'.φ = m.φ := m'.cart.1.lift_fst _ _ _
  have hψ₀ : ψ ≫ o'.A.hom = o'.A.hom := m'.cart.1.lift_snd _ _ _
  have hψ' : ψ ≫ o'.A.hom = o'.A.hom ≫ 𝟙 S' := by rw [Category.comp_id]; exact hψ₀
  have n : IsGrpPullback o'.A o.A (𝟙 S' ≫ f) (ψ ≫ m'.φ) := by rw [hψ, Category.id_comp]; exact m.cart
  obtain ⟨ψ₂, sq⟩ := exists_isSquare hψ'
  have e : m.φ₂ = ψ₂ ≫ m'.φ₂ := isSquare_unique m.sq (hψ ▸ isSquare_comp sq m'.sq)
  have hact : ∀ c, (o'.act.act c).left ≫ ψ = ψ ≫ (o'.act.act c).left := by
    intro c
    apply m'.cart.1.hom_ext
    · rw [Category.assoc, hψ, m.act, Category.assoc, m'.act, ← Category.assoc, hψ]
    · rw [Category.assoc, hψ₀, Over.w, Category.assoc, Over.w, hψ₀]
  have heta : ∀ y, (o'.eta y).left ≫ ψ = 𝟙 S' ≫ (o'.eta y).left := by
    intro y
    apply m'.cart.1.hom_ext
    · rw [Category.assoc, hψ, m.eta, Category.id_comp, m'.eta]
    · rw [Category.assoc, hψ₀, Category.id_comp]
  exact ⟨{ φ := ψ
           φ₂ := ψ₂
           cart := m'.cart.cancel n hψ'
           sq := sq
           act := hact
           pol := LBIso.trans o'.isLB (pull_isLB o.isLB _) (pull_isLB o'.isLB _) m.pol
             (LBIso.symm (lbIso_pull_comp m'.pol ψ₂ e))
           eta := heta }, hψ⟩

theorem objMap_φ_unique : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R)
    (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (S S' : Scheme.{0}) (s : S ⟶ Sp R) (s' : S' ⟶ Sp R) (o' : Obj b N s')
    (o : Obj b N s) (f : S' ⟶ S) (m m' : ObjMap o' o f), m.φ = m'.φ := by
  intro p _ D R _ b N hN hNp S S' s s' o' o f m m'
  obtain ⟨a, ha⟩ := exists_auto m m'
  have h1 := GlobalTheory.UPel.HT.Rigid.eq_id p D R b N hN hNp S' s' o' a
  rw [← ha, h1, Category.id_comp]

end GlobalTheory.UPel.HT.MapUniq
