import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.InUQT
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittChartDescendLevelStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MapHBijOfRes
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatOfEtalePoly

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Ls CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.LsG CrystallineSemistableComparison.Pb.SubquotientResolution CrystallineSemistableComparison.Pb.LsQ

namespace GlobalTheory.CompanionTheory.GradedDegreeZeroIsLocal

variable {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l] {O : Type} [CommRing O]
  {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {ρ : O →+* k}

def polyV {m : ℕ} {𝒱 : Set X.Opens} (P : Poly (sP (stF q ρ m 𝒱))) : Poly (sV q ρ m 𝒱) where
  P := P.P
  j := P.j
  X := P.X
  X_mem := P.X_mem
  univ := P.univ
  span := P.span

def frameV {m : ℕ} {𝒱 : Set X.Opens} {d : ℕ} (E : Frame (sP (stF q ρ m 𝒱)) d) : Frame (sV q ρ m 𝒱) d where
  D := E.D
  ne := E.ne
  τ := E.τ
  mem := E.mem
  add := E.add
  nat := E.nat
  bij := E.bij

theorem nil_m (k : Type) [Field k] [CharP k l] [PerfectRing k l] (m : ℕ) : IsNilpotent ((l : ℕ) : Wc.Wm l k m) := ⟨m, by
  rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {(l : WittVector l k) ^ m})), ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_span_singleton_self _⟩

theorem o_bij {n : ℕ} (hn : n ≠ 0) (𝒱 : Set X.Opens) (T : (stF q ρ (n + 1) 𝒱).FullSubcategory) :
    Function.Bijective (((mqS q ρ hn 𝒱).o (IdF.span _ ((l : WittVector l k) ^ n)) fun _ => le_rfl).τ T) := by
  constructor
  · intro x y hxy
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective (show T.obj.B ⧸ lI n T.obj from x)
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective (show T.obj.B ⧸ lI n T.obj from y)
    exact congrArg Subtype.val hxy
  · rintro ⟨z, hz⟩
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨Ideal.Quotient.mk (lI n T.obj) a, Subtype.ext rfl⟩

theorem iso_bij {m : ℕ} {T T' : Thick (Wc.L l (B.schFn q) ρ m)} (e : T ≅ T') : Function.Bijective e.hom.φ := by
  refine Function.bijective_iff_has_inverse.2 ⟨e.inv.φ, fun x => ?_, fun x => ?_⟩
  · exact RingHom.congr_fun (congrArg (fun f => f.φ) e.hom_inv_id) x
  · exact RingHom.congr_fun (congrArg (fun f => f.φ) e.inv_hom_id) x

set_option maxHeartbeats 1000000 in

theorem local_bij (q : X ⟶ Spec (CommRingCat.of O)) (ρ : O →+* k) {n : ℕ} (hn : n ≠ 0) {W : X.Opens} {d : ℕ}
    (cW : Coord q W d) (j : ℕ) :
    Function.Bijective (((mqS q ρ hn {W}).o (IdF.span _ ((l : WittVector l k) ^ n)) (fun _ => le_rfl)).pull j) := by
  have hl0 : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  obtain ⟨c', hF', -⟩ := GlobalTheory.CompanionTheory.FlatChartP.exists_flat_chart (Wc.pd l k (n + 1)) l hl0 (nil_m k (n + 1)) q
    ((Wc.res l k (n + 1)).comp ρ) cW
  obtain ⟨c, e, hec, hfl⟩ := GlobalTheory.T.witt_chart_descend_level q ρ hn c'
  have hF : FlatT c.D := hfl (GlobalTheory.T.flat_thickening_quotient l k O (B.schFn q) ρ n hn c'.D hF')
  obtain ⟨PA, hPA⟩ := poly_all (Wc.pd l k n) l hl0 q ((Wc.res l k n).comp ρ) FlatT (Or.inr rfl) {W}
  obtain ⟨PB, hPB⟩ := poly_all (Wc.pd l k (n + 1)) l hl0 q ((Wc.res l k (n + 1)).comp ρ) FlatT (Or.inr rfl) {W}
  have hgA := GlobalTheory.CompanionTheory.ChartMaps.good c
  have hgB := GlobalTheory.CompanionTheory.ChartMaps.good c'
  have hQA : ∀ T, stF q ρ n {W} T → InU W T := by
    rintro T ⟨-, V, rfl, hV⟩
    exact hV
  have hQB : ∀ T, stF q ρ (n + 1) {W} T → InU W T := by
    rintro T ⟨-, V, rfl, hV⟩
    exact hV
  have hDA : stF q ρ n {W} c.D := ⟨hF, W, rfl, c.inV⟩
  have hDB : stF q ρ (n + 1) {W} c'.D := ⟨hF', W, rfl, c'.inV⟩
  let E : Frame (sV q ρ n {W}) d := frameV (c.frame hgA _ hQA hDA)
  let E' : Frame (sV q ρ (n + 1) {W}) d := frameV (c'.frame hgB _ hQB hDB)
  let M := mqS q ρ hn {W}
  let e' : E.D ⟶ M.G.obj E'.D := ObjectProperty.homMk e.hom
  have he : M.Fr E E' e' := by
    intro i T s₁ s₂
    change M.ρ T (qφ s₂.hom (e.hom.φ (c.t i)) - qφ s₁.hom (e.hom.φ (c.t i))) =
      Ideal.Quotient.mk _ (s₂.hom.φ (c'.t i) - s₁.hom.φ (c'.t i))
    rw [hec]
    rfl
  let b : ℤ → IdF (sV q ρ (n + 1) {W}).A := fun _ => IdF.span _ ((l : WittVector l k) ^ n)
  exact GlobalTheory.CompanionTheory.LocCmp.localComparison M (polyV PA) (polyV PB) E E' e' he b (fun _ _ => le_rfl) 0 (hPA 0).2.1
    (fun r _ => ((hPB r).2.2 (Ideal.Quotient.mk _ ((l : WittVector l k) ^ n))).2.2)
    (fun r' _ _ => (o_bij hn {W} E'.D).comp (iso_bij e)) j

end GlobalTheory.CompanionTheory.GradedDegreeZeroIsLocal

end
