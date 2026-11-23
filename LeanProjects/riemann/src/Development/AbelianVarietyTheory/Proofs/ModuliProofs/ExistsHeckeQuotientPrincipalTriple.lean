import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SeesawTrivialityOnDenseFibresProductAbelianStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TheoremOfCubePolAbelianScheme
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LbPowDescendsOfIsotropicOfLaws
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubeDescendsAlongEtaleIsogeny
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaOfTranslDiff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecImageNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsQuotientByFiniteGroupOfPoints

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

open CechPic

theorem exists_heckeQuotient_triple_of_laws : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (t : SAB H (Sp k)) (g p : ℕ) (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ t.G)), 0 < p → IsProper t.G.hom → SmoothOfRelativeDimension g t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → (∀ x ∈ C, ∀ a, x ≫ t.act.act a ∈ C) → (∀ x ∈ C, x ^ p ^ 2 = 1) → (∀ x ∈ C, ∀ y ∈ C, Out.WeilIs t.G t.PP.L ((p ^ 2 : ℕ) : ℤ) x y 1) → Nat.card C = p ^ (2 * g) → ∃ (t' : SAB H (Sp k)) (ψ : t.G ⟶ t'.G), IsProper t'.G.hom ∧ Out.RelAmple t'.G t'.PP.L ∧ Out.KTriv t'.G t'.PP.L ∧ IsMonHom ψ ∧ IsFinite ψ.left ∧ Etale ψ.left ∧ Surjective ψ.left ∧ (∀ x : 𝟙_ (Over (Sp k)) ⟶ t.G, x ≫ ψ = 1 ↔ x ∈ C) ∧ (∀ a, t.act.act a ≫ ψ = ψ ≫ t'.act.act a) ∧ LBIso (lbPow t.PP.L (p ^ 2)) (t'.PP.L.pull ψ.left) := by
  intro laws E _ _ _ H k _ _ _ t g p C hp hprop hsm hamp hK hst hpow
    hweil hcard
  have glob : Out.GlobalFnsSt := laws.globalFns
  have cube := GlobalTheory.Moduli.cube_of_isLB
  have cubeDesc := GlobalTheory.cube_descends_along_etale_isogeny glob
  have quot := GlobalTheory.exists_quotient_by_finite_group_of_points laws
  have split := GlobalTheory.lbPow_descends_of_isotropic_of_laws laws
  have princ := GlobalTheory.kTriv_of_descent laws
  have amp := GlobalTheory.relAmple_finite_pow_iso
  have prim := GlobalTheory.PrimNorm.exists_primitive_normalisation glob
  have seesaw := GlobalTheory.T.seesaw_triviality_on_dense_fibres_product_abelian glob
  have hA : IsAbelianScheme t.G := AbelianSchemeGerms.isAbelianScheme_of_proper t.G t.semi
  have hL := t.PP.isLB
  let P : Out.PolAV (Sp k) :=
    { A := t.G, isAb := hA, g := g, smoothDim := hsm, L := t.PP.L, isLB := hL,
      rigid := ⟨t.PP.rig, t.PP.rigGen⟩, sym := sym_of_isSymmetric t.PP t.sym, ample := hamp, ktriv := hK }
  have hn : 0 < p ^ 2 := pow_pos hp 2
  have hfin : Finite C := Nat.finite_of_card_ne_zero (by rw [hcard]; exact (pow_pos hp _).ne')
  obtain ⟨B, gB, ψ, hB, hψ, hf, he, hs, hker, huniv⟩ :
      ∃ (B : Over (Sp k)) (_ : GrpObj B) (ψ : t.G ⟶ B), IsAbelianScheme B ∧ IsMonHom ψ ∧ IsFinite ψ.left ∧
        Etale ψ.left ∧ Surjective ψ.left ∧ (∀ x : 𝟙_ (Over (Sp k)) ⟶ t.G, x ≫ ψ = 1 ↔ x ∈ C) ∧
        ∀ (Y : Over (Sp k)) (f : t.G ⟶ Y), (∀ x ∈ C, ((toUnit t.G ≫ x) * 𝟙 t.G) ≫ f = f) →
          ∃! f' : B ⟶ Y, ψ ≫ f' = f := quot k P C hfin
  have := hB.comm
  obtain ⟨M, hM, hiso⟩ : ∃ M : LB B.left, M.IsLB ∧ LBIso (lbPow t.PP.L (p ^ 2)) (M.pull ψ.left) :=
    split k P (p ^ 2) C B ψ hn (Nat.cast_ne_zero.2 hn.ne') hpow hweil hψ hf he hs hker
  have hΘ : ∃ s : LB.Gen (Theta B M), s.IsGen :=
    cubeDesc k t.G B ψ M hA hB hM hψ hf he hs (cube _ P (M.pull ψ.left) (pull_isLB hM _))
  have hn' : (lbPow t.PP.L (p ^ 2)).IsLB := LB.isLB_linComb hL _ _
  have hid : IsFinite (𝟙 t.G : t.G ⟶ t.G).left := by rw [Over.id_left]; infer_instance
  have a₁ : Out.RelAmple t.G (lbPow t.PP.L (p ^ 2)) :=
    (amp _ t.G t.G (𝟙 _) t.PP.L (p ^ 2) hn hA hA hL hid).2.1.2 hamp

  have hMamp : Out.RelAmple B M :=
    (amp _ t.G B ψ M 1 one_pos hA hB hM hf).2.2.1 inferInstance hs
      ((amp _ t.G t.G (𝟙 _) _ 1 one_pos hA hA hn' hid).2.2.2 _ (pull_isLB hM _) hiso a₁)

  have fac : ∀ (Y : Over (Sp k)) [GrpObj Y] (f : t.G ⟶ Y) [IsMonHom f], (∀ x ∈ C, x ≫ f = 1) →
      ∃ f' : B ⟶ Y, ψ ≫ f' = f := fun Y _ f _ h =>
    (huniv Y f fun x hx => by
      rw [MonObj.mul_comp, Category.assoc, h x hx, MonObj.comp_one, _root_.one_mul, Category.id_comp]).exists
  have canc : ∀ (Y : Over (Sp k)) (f f' : B ⟶ Y), ψ ≫ f = ψ ≫ f' → f = f' := fun Y f f' h =>
    (huniv Y (ψ ≫ f) fun x hx => by
      rw [← Category.assoc, MonObj.mul_comp, Category.assoc, (hker x).2 hx, MonObj.comp_one, _root_.one_mul,
        Category.id_comp]).unique rfl h.symm
  have hact : ∀ a, ∃ f' : B ⟶ B, ψ ≫ f' = t.act.act a ≫ ψ := fun a => by
    have := t.act.hom a
    exact fac B _ fun x hx => by rw [← Category.assoc]; exact (hker _).2 (hst x hx a)
  choose α hα using hact
  let act : OAct (𝓞 E) B :=
    { act := α
      hom := fun a => laws.rigidity _ B B hB hB _ (by
        have := t.act.hom a
        rw [← IsMonHom.one_hom ψ, Category.assoc, hα, ← Category.assoc, IsMonHom.one_hom])
      one := canc _ _ _ (by rw [hα, t.act.one, Category.id_comp, Category.comp_id])
      mul := fun a b => canc _ _ _ (by
        rw [hα, t.act.mul, ← Category.assoc ψ, hα, Category.assoc, Category.assoc, hα])
      add := fun a b => canc _ _ _ (by rw [hα, t.act.add, MonObj.mul_comp, MonObj.comp_mul, hα, hα]) }
  have hαhom : ∀ a, IsMonHom (α a) := act.hom

  set l := cls t.PP.L hL with hl
  set m := cls M hM with hm
  have hψm : pull ψ.left m = (p ^ 2) • l := by
    rw [← cls_lbPow hL (p ^ 2) (LB.isLB_linComb hL _ _)]
    exact ((cls_eq_iff _ (pull_isLB hM _)).2 hiso).symm
  have lamψ : ∀ {T : Over (Sp k)} (u v : T ⟶ t.G), lam m (u ≫ ψ) (v ≫ ψ) = (p ^ 2) • lam l u v := fun u v => by
    rw [← lam_pull, hψm, lam_nsmul]

  have hpowhom : IsMonHom (𝟙 t.G ^ p ^ 2) := laws.rigidity _ _ _ hA hA _ (by
    have e₁ : (η[t.G] : 𝟙_ _ ⟶ t.G) = 1 := by rw [Hom.one_def]; simp
    rw [MonObj.comp_pow, Category.comp_id, e₁, one_pow])
  obtain ⟨π, hπ⟩ := fac t.G (𝟙 t.G ^ p ^ 2) fun x hx => by rw [MonObj.comp_pow, Category.comp_id, hpow x hx]
  have hπψ : π ≫ ψ = 𝟙 B ^ p ^ 2 := canc _ _ _ (by
    rw [← Category.assoc, hπ, MonObj.pow_comp, MonObj.comp_pow, Category.id_comp, Category.comp_id])
  have adj : ∀ a, LBIso (cubeLB B ![fst B B ≫ act.act a, snd B B] M)
      (cubeLB B ![fst B B, snd B B ≫ act.act (H.bar a)] M) := by
    intro a
    have := hαhom a
    have := hαhom (H.bar a)
    have adjA : ∀ {T : Over (Sp k)} (u v : T ⟶ t.G), lam l (u ≫ t.act.act a) v = lam l u (v ≫ t.act.act (H.bar a)) := by
      intro T u v
      have h := (cls_eq_iff (LB.isLB_linComb hL _ _) (LB.isLB_linComb hL _ _)).2 (t.adj a)
      have h' := congrArg (pull (lift u v).left)
        ((cls_cube_two hL _ _ _).symm.trans (h.trans (cls_cube_two hL _ _ _)))
      simpa only [pull_lam, lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc] using h'
    have adjψ : ∀ {T : Over (Sp k)} (u v : T ⟶ t.G),
        lam m (u ≫ ψ ≫ α a) (v ≫ ψ) = lam m (u ≫ ψ) (v ≫ ψ ≫ α (H.bar a)) := by
      intro T u v
      rw [hα, hα, ← Category.assoc, ← Category.assoc, lamψ, lamψ, adjA]
    have h₁ : (cubeLB B ![fst B B ≫ α a, snd B B] M).IsLB := LB.isLB_linComb hM _ _
    have h₂ : (cubeLB B ![fst B B, snd B B ≫ α (H.bar a)] M).IsLB := LB.isLB_linComb hM _ _
    have hN := LB.isLB_div h₂ h₁
    have val : ∀ {T : Over (Sp k)} (x y : T ⟶ B), lam m (x ≫ α a) y = lam m x (y ≫ α (H.bar a)) →
        ∃ s : ((LB.div (cubeLB B ![fst B B, snd B B ≫ α (H.bar a)] M)
          (cubeLB B ![fst B B ≫ α a, snd B B] M)).pull (lift x y).left).Gen, s.IsGen := by
      intro T x y h
      refine (cls_eq_zero_iff (pull_isLB hN _)).1 ?_
      rw [cls_pull hN, cls_div h₂ h₁, cls_cube_two hM, cls_cube_two hM, map_sub, pull_lam, pull_lam, lift_fst,
        lift_snd, lift_fst_assoc, lift_snd_assoc, ← hm, h, sub_self]
    refine seesaw k B B _ M hB hB hM hMamp hN (val _ _ ?_) ?_ (val _ _ ?_)
    · rw [MonObj.one_comp, lam_one_left, lam_one_left]
    · have hs' : Surjective (𝟙 t.G ^ p ^ 2).left := (laws.mulN _ P (p ^ 2) hn).2.2.1
      have hs'' : Surjective ((𝟙 t.G ^ p ^ 2) ≫ ψ).left := by rw [Over.comp_left]; infer_instance
      refine dense_image_points ((𝟙 t.G ^ p ^ 2) ≫ ψ) _ fun u => val _ _ ?_
      have h := adjψ (toUnit B ≫ u) π
      rw [← Category.assoc π, hπψ, MonObj.pow_comp, lam_pow_right hM hΘ, lam_pow_right hM hΘ] at h
      rw [MonObj.pow_comp, MonObj.comp_pow, MonObj.comp_pow, MonObj.pow_comp, lam_pow_left hM hΘ,
        lam_pow_left hM hΘ]
      simpa only [Category.assoc, Category.id_comp] using h
    · rw [MonObj.one_comp, lam_one_right, lam_one_right]
  obtain ⟨PP, cub, hsym, hPP, -, hprim, hadj⟩ := prim E H _ B act M hB hM hΘ adj
  have hP' := PP.isLB
  have hpull : pull ψ.left (cls PP.L hP') = (p ^ 2) • l := by
    have h := (cls_eq_iff hL (LB.isLB_linComb hL _ _)).2 t.prim
    have h' := (cls_eq_iff hP' (LB.isLB_linComb hM _ _)).2 hPP
    have e : l = lam l (𝟙 _) (t.act.act H.w0) := h.trans (cls_cube_two hL _ _ _)
    have e' : cls PP.L hP' = lam m (𝟙 _) (α H.w0) := h'.trans (cls_cube_two hM _ _ _)
    rw [e', pull_lam, hα, Category.comp_id, ← Category.id_comp ψ, ← Category.assoc, Category.comp_id, lamψ, ← e]
  have hfinal : LBIso (lbPow t.PP.L (p ^ 2)) (PP.L.pull ψ.left) := by
    rw [← cls_eq_iff hn' (pull_isLB hP' _), cls_lbPow hL, cls_pull hP', hpull]
  have a₂ : Out.RelAmple t.G (PP.L.pull ψ.left) :=
    (amp _ t.G t.G (𝟙 _) _ 1 one_pos hA hA hn' hid).2.2.2 _ (pull_isLB hP' _) hfinal a₁
  have a₃ : Out.RelAmple B PP.L :=
    (amp _ t.G B ψ PP.L 1 one_pos hA hB hP' hf).2.2.1 inferInstance hs a₂
  have hc : Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ t.G // x ≫ ψ = 1} = (p ^ 2) ^ g := by
    rw [← pow_mul, ← hcard]
    exact Nat.card_congr (Equiv.subtypeEquivRight hker)
  have hlam : LBIso (abelian₂ t.G (lbPow t.PP.L (p ^ 2))) (abelian₂ t.G (PP.L.pull ψ.left)) := by
    refine (cls_eq_iff (LB.isLB_linComb hn' _ _) (LB.isLB_linComb (pull_isLB hP' _) _ _)).1 ?_
    refine (cls_cube_two hn' _ _ _).trans (Eq.trans ?_ (cls_cube_two (pull_isLB hP' _) _ _ _).symm)
    rw [(cls_eq_iff hn' (pull_isLB hP' _)).2 hfinal]
  have a₄ : Out.KTriv B PP.L := princ k P (p ^ 2) B ψ PP.L hn hB hP' hψ hf he hs hc hlam
  exact ⟨{ G := B, semi := isSemiAbelian_of_isAbelianScheme B hB, act := act, PP := PP, cub := cub, sym := hsym,
           adj := hadj, prim := hprim }, ψ, hB.proper, a₃, a₄, hψ, hf, he, hs, hker, fun a => (hα a).symm, hfinal⟩

end GlobalTheory
