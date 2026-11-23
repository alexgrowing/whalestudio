import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.TransCancel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodsSpanPureDecomposition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentHomQuotientGaloisGroupScheme

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

private theorem isIso_hecke {G : GDatum} {R : Type} [CommRing R] [Algebra ℚ R] {gb : GBase G R} {N k : ℕ} {S : Scheme.{0}}
    {s : S ⟶ Sp R} {o' : GObj gb (N * k) s} {o : GObj gb N s} {ψ : o'.A ⟶ o.A}
    (h : IsGHecke (k • (LinearMap.id : G.La →ₗ[G.O] G.La)) (k ^ 2) k N o' o ψ) : IsIso ψ := by
  obtain ⟨f, -, e⟩ := GlobalTheory.HomDescent.exists_desc S o'.A o.A o'.A
    (gHeckeSub o' (k • (LinearMap.id : G.La →ₗ[G.O] G.La)) N) ψ h.isMonHom h.cover (𝟙 _) inferInstance
    (fun a ha => by rw [gHeckeSub_smul_id_eq_one o' a ha, Category.comp_id])
  have : Epi ψ.left := GlobalTheory.GaloisCartDesc.epi_of_isGaloisCover h.cover
  refine ⟨f, e, ?_⟩
  apply Over.OverMorphism.ext
  rw [← cancel_epi ψ.left, ← Over.comp_left, ← Over.comp_left, ← Category.assoc, e]
  simp

private theorem pol_hecke {G : GDatum} {R : Type} [CommRing R] [Algebra ℚ R] {gb : GBase G R} {N k : ℕ} {S : Scheme.{0}}
    {s : S ⟶ Sp R} (hk : 0 < k) {o' : GObj gb (N * k) s} {o : GObj gb N s} {ψ : o'.A ⟶ o.A}
    (h : IsGHecke (k • (LinearMap.id : G.La →ₗ[G.O] G.La)) (k ^ 2) k N o' o ψ) :
    LBIso o'.P (o.P.pull (Hecke.sq2 ψ)) := by
  have h0 := h.pol
  rw [Nat.div_self (pow_pos hk 2)] at h0
  obtain ⟨h0⟩ := h0
  have l1 : (Hecke.lbPow o'.P 1).IsLB := LB.isLB_linComb o'.isLB _ _
  have l2 : (o'.P.pull (𝟙 _)).IsLB := pull_isLB o'.isLB _
  have i1 : LBIso (o'.P.pull (𝟙 _)) (Hecke.lbPow o'.P 1) := by
    refine (GlobalTheory.PrimNorm.lbIso_iff o'.isLB _ _ _ _).2 ?_
    simp
  exact LBIso.trans o'.isLB l2 (pull_isLB o.isLB _) (GlobalTheory.SiegLower.lbIso_pull_id o'.isLB)
    (LBIso.trans l2 l1 (pull_isLB o.isLB _) i1 h0)

private theorem aux (hMap : MapOfIso) (hSelf : TransSelf) (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G)
    (R : Type) [Field R] [Algebra ℚ R] (gb : GBase D.toG R) (N : Lv p) (c : ℕ) (hc : c.Coprime p)
    (X : GenModel gb N.1) (X' : GenModel gb (N.1 * c)) :
    ∃ π Φ, Wit L 1 X' X π Φ ∧ IsFinite π ∧ Etale π ∧ Surjective π := by
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have cpos : 0 < c := Nat.pos_of_ne_zero fun h => by subst h; rw [Nat.coprime_zero_left] at hc; omega
  have hN : 0 < N.1 := by have := N.2.1; omega
  obtain ⟨π, ⟨hπ, o', ψ, hG, ⟨m'⟩⟩, hf, he, hs⟩ := HeckeGen.exists_gHeckeMap_finite_etale_surjective p D R gb
    (c • LinearMap.id) (c ^ 2) c N.1 (hc.pow_left 2) hc N.2.1 N.2.2
    (fun x y => by simp [LinearMap.smul_apply]; ring) (fun x => ⟨x, rfl⟩) dvd_rfl X X'
  have hI : IsIso ψ := isIso_hecke hG
  obtain ⟨m, -⟩ := hMap D.toG R gb X'.X X'.s N.1 (X'.univ.forgetMul hN cpos) o' ψ hI hG.isMonHom hG.act
    (pol_hecke cpos hG) (fun y => (hG.eta y).symm)
  obtain ⟨φ⟩ := Unique.gObjMap_comp m m'
  rw [Category.id_comp] at φ
  exact ⟨π, (𝟙 X'.univ.A : X'.univ.A ⟶ X'.univ.A).left ≫ φ.φ,
    ⟨hπ, X'.univ.forgetMul hN cpos, 𝟙 _, φ, (hSelf p D G L R gb X'.X X'.s N).2 c hN cpos X'.univ, rfl⟩, hf, he, hs⟩

theorem UpperTheory.Gal.G3.pWitForget :
    MapOfIso → TransSelf → WitForget := by
  intro hMap hSelf p _ D G L R _ _ gb N M hdiv X X'
  obtain ⟨M, hM⟩ := M
  obtain ⟨c, rfl⟩ := hdiv
  exact aux hMap hSelf p D G L R gb N c (Nat.Coprime.coprime_mul_left hM.2) X X'
