import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsOActDescendOfEtaleIsogeny
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TrivOfAxesTrivPullbackEtaleIsogenyStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubeOfExistsRelAmple
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmplePrincipalDescendedBundleNoetherianStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkFam

open CechPic

theorem exists_quotient_triple_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (t : SAB H (Sp R)) (g p : ℕ) (B : Over (Sp R)) [GrpObj B] (ψ : t.G ⟶ B) (M : LB B.left), (∀ m : ℕ, 0 < m → IsUnit (m : R)) → 0 < p → IsProper t.G.hom → SmoothOfRelativeDimension g t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → IsAbelianScheme B → M.IsLB → IsMonHom ψ → IsFinite ψ.left → Etale ψ.left → Surjective ψ.left → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Sp R), Nat.card {z : Over.mk x ⟶ t.G // z ≫ ψ = 1} = p ^ (2 * g) ∧ ∀ z : Over.mk x ⟶ t.G, z ≫ ψ = 1 → z ^ p ^ 2 = 1 ∧ ∀ a, (z ≫ t.act.act a) ≫ ψ = 1) → LBIso (lbPow t.PP.L (p ^ 2)) (M.pull ψ.left) → ∃ (t' : SAB H (Sp R)) (ψ' : t.G ⟶ t'.G), IsProper t'.G.hom ∧ Out.RelAmple t'.G t'.PP.L ∧ Out.KTriv t'.G t'.PP.L ∧ IsIsogT t t' p ψ' ∧ ∀ (T : Over (Sp R)) (z : T ⟶ t.G), z ≫ ψ' = 1 ↔ z ≫ ψ = 1 := by
  intro E _ _ _ H R _ _ _ t g p B _ ψ M hR hp hprop hsm hamp hK hB hM hψ hf he hs hker hiso
  have laws : Out.Laws := GlobalTheory.firstFiveLaws.1
  have hA : IsAbelianScheme t.G := AbelianSchemeGerms.isAbelianScheme_of_proper t.G t.semi
  have hL := t.PP.isLB
  let P : Out.PolAV (Sp R) :=
    { A := t.G, isAb := hA, g := g, smoothDim := hsm, L := t.PP.L, isLB := hL,
      rigid := ⟨t.PP.rig, t.PP.rigGen⟩, sym := sym_of_isSymmetric t.PP t.sym, ample := hamp, ktriv := hK }
  have hn : 0 < p ^ 2 := pow_pos hp 2
  have := hB.comm
  have hred : IsReduced (Sp R) := inferInstance
  have hc : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Sp R),
      Nat.card {z : Over.mk x ⟶ t.G // z ≫ ψ = 1} = (p ^ 2) ^ g := fun k _ _ x => by
    rw [← pow_mul]; exact (hker k x).1
  have hMamp : Out.RelAmple B M := (GlobalTheory.T.relAmple_principal_descendedBundle_noetherian R P (p ^ 2) B ψ M hR hn hB hM hψ hf he hs hc hiso).1
  have hΘ : ∃ s : LB.Gen (Theta B M), s.IsGen := cube_of_relAmple _ B M hB hM hMamp
  obtain ⟨act, hact⟩ := GlobalTheory.exists_oAct_descend_of_etale_isogeny (𝓞 E) (Sp R) t.G B ψ t.act hA hB hψ hf he hs
    fun k _ _ x z c hz => ((hker k x).2 z hz).2 c
  have hα : ∀ a, ψ ≫ act.act a = t.act.act a ≫ ψ := fun a => (hact a).symm
  have hunit : IsUnit ((p ^ 2 : ℕ) : Γ(Sp R, ⊤)) := by
    have h := (hR _ hn).map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    rwa [map_natCast] at h
  set l := cls t.PP.L hL with hl
  set m := cls M hM with hm
  have hψm : pull ψ.left m = (p ^ 2) • l := by
    rw [← cls_lbPow hL (p ^ 2) (LB.isLB_linComb hL _ _)]
    exact ((cls_eq_iff _ (pull_isLB hM _)).2 hiso).symm
  have lamψ : ∀ {T : Over (Sp R)} (u v : T ⟶ t.G), lam m (u ≫ ψ) (v ≫ ψ) = (p ^ 2) • lam l u v := fun u v => by
    rw [← lam_pull, hψm, lam_nsmul]
  have adj : ∀ a, LBIso (cubeLB B ![fst B B ≫ act.act a, snd B B] M)
      (cubeLB B ![fst B B, snd B B ≫ act.act (H.bar a)] M) := by
    intro a
    have := act.hom a
    have := act.hom (H.bar a)
    have adjA : ∀ {T : Over (Sp R)} (u v : T ⟶ t.G), lam l (u ≫ t.act.act a) v = lam l u (v ≫ t.act.act (H.bar a)) := by
      intro T u v
      have h := (cls_eq_iff (LB.isLB_linComb hL _ _) (LB.isLB_linComb hL _ _)).2 (t.adj a)
      have h' := congrArg (pull (lift u v).left)
        ((cls_cube_two hL _ _ _).symm.trans (h.trans (cls_cube_two hL _ _ _)))
      simpa only [pull_lam, lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc] using h'
    have adjψ : ∀ {T : Over (Sp R)} (u v : T ⟶ t.G),
        lam m ((u ≫ ψ) ≫ act.act a) (v ≫ ψ) = lam m (u ≫ ψ) ((v ≫ ψ) ≫ act.act (H.bar a)) := by
      intro T u v
      rw [Category.assoc, Category.assoc, hα, hα, ← Category.assoc, ← Category.assoc, lamψ, lamψ, adjA]
    have h₁ : (cubeLB B ![fst B B ≫ act.act a, snd B B] M).IsLB := LB.isLB_linComb hM _ _
    have h₂ : (cubeLB B ![fst B B, snd B B ≫ act.act (H.bar a)] M).IsLB := LB.isLB_linComb hM _ _
    have hN := LB.isLB_div h₂ h₁
    have val : ∀ {T : Over (Sp R)} (x y : T ⟶ B), lam m (x ≫ act.act a) y = lam m x (y ≫ act.act (H.bar a)) →
        ∃ s : ((LB.div (cubeLB B ![fst B B, snd B B ≫ act.act (H.bar a)] M)
          (cubeLB B ![fst B B ≫ act.act a, snd B B] M)).pull (lift x y).left).Gen, s.IsGen := by
      intro T x y h
      refine (cls_eq_zero_iff (pull_isLB hN _)).1 ?_
      rw [cls_pull hN, cls_div h₂ h₁, cls_cube_two hM, cls_cube_two hM, map_sub, pull_lam, pull_lam, lift_fst,
        lift_snd, lift_fst_assoc, lift_snd_assoc, ← hm, h, sub_self]
    refine GlobalTheory.T.triv_of_axes_triv_pullback_etale_isogeny (Sp R) t.G B ψ M _ (p ^ 2) hA hB hM hMamp hN hψ hf he hs hn hunit
      (fun k _ _ x z hz => ((hker k x).2 z hz).1) (val _ _ ?_) (val _ _ ?_) ?_
    · rw [MonObj.one_comp, lam_one_left, lam_one_left]
    · rw [MonObj.one_comp, lam_one_right, lam_one_right]
    · have e : ψ ⊗ₘ ψ = lift (fst t.G t.G ≫ ψ) (snd t.G t.G ≫ ψ) := by ext <;> simp
      rw [e]
      exact val _ _ (adjψ _ _)
  obtain ⟨PP, cub, hsym, hPP, -, hprim, hadj⟩ :=
    GlobalTheory.PrimNorm.exists_primitive_normalisation laws.globalFns E H _ B act M hB hM hΘ adj
  have hP' := PP.isLB
  have hpull : pull ψ.left (cls PP.L hP') = (p ^ 2) • l := by
    have h := (cls_eq_iff hL (LB.isLB_linComb hL _ _)).2 t.prim
    have h' := (cls_eq_iff hP' (LB.isLB_linComb hM _ _)).2 hPP
    have e : l = lam l (𝟙 _) (t.act.act H.w0) := h.trans (cls_cube_two hL _ _ _)
    have e' : cls PP.L hP' = lam m (𝟙 _) (act.act H.w0) := h'.trans (cls_cube_two hM _ _ _)
    rw [e', pull_lam, hα, Category.comp_id, ← Category.id_comp ψ, ← Category.assoc, Category.comp_id, lamψ, ← e]
  have hn' : (lbPow t.PP.L (p ^ 2)).IsLB := LB.isLB_linComb hL _ _
  have hfinal : LBIso (lbPow t.PP.L (p ^ 2)) (PP.L.pull ψ.left) := by
    rw [← cls_eq_iff hn' (pull_isLB hP' _), cls_lbPow hL, cls_pull hP', hpull]
  obtain ⟨a₃, a₄⟩ := GlobalTheory.T.relAmple_principal_descendedBundle_noetherian R P (p ^ 2) B ψ PP.L hR hn hB hP' hψ hf he hs hc hfinal
  exact ⟨{ G := B, semi := isSemiAbelian_of_isAbelianScheme B hB, act := act, PP := PP, cub := cub, sym := hsym,
           adj := hadj, prim := hprim }, ψ, hB.proper, a₃, a₄, ⟨hψ, hf, he, hs, hact, hfinal⟩, fun _ _ => Iff.rfl⟩

end GlobalTheory.HkFam
