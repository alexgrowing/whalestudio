import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiFor
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectPullbackBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PushSecOfLeft

noncomputable section

namespace GlobalTheory.HTMkObj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor
open GlobalTheory.SiegelPull ReciprocityTheory.ChartRestriction.G.Pdiv

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {S : Scheme.{0}}

theorem lieAt_of_lieHer (b : Base D R) {A : Over S} [GrpObj A] {act : OActN D.O A} {R' : Type} [CommRing R']
    {β : R →+* R'} {x : Sp R' ⟶ S} (h : LieHer b act β x) : LieAt b act β x := by
  have H := (h R' (RingHom.id R')).1
  have e : spMap (RingHom.id R') = 𝟙 _ := Spec.map_id _
  simp only [e, Category.id_comp, RingHom.id_comp] at H
  exact H

theorem lieMult_of_lieHer (b : Base D R) {A : Over S} [GrpObj A] {act : OActN D.O A} (k : Type) [Field k]
    [IsAlgClosed k] {β : R →+* k} {x : Sp k ⟶ S} (h : LieHer b act β x) (i : Fin D.a) :
    LieMult (act.toF D) x (β.comp (b.t i)) D.m := by
  have H := (h k (RingHom.id k)).2 k (RingHom.id k) i
  have e : spMap (RingHom.id k) = 𝟙 _ := Spec.map_id _
  simp only [e, Category.id_comp, RingHom.id_comp] at H
  exact H

end GlobalTheory.HTMkObj

namespace GlobalTheory.HTMkObj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor
open GlobalTheory.SiegelPull ReciprocityTheory.ChartRestriction.G.Pdiv
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

theorem exists_obj_of_locus : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (h M : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Scheme.{0}) (s₁ : S ⟶ Sp B) (t : S ⟶ Sp R) (c : SiegPre h M ζ s₁) (e : ℕ), e.Coprime p → SiegKerBy c e → ∀ (X : Scheme.{0}) (πX : X ⟶ S) (AX : Over X) [GrpObj AX] [IsCommMonObj AX] (φX : AX.left ⟶ c.A.left) (φ₂X : (G2 AX).left ⟶ (G2 c.A).left) (actX : OActN D.O AX) (ηX : D.La → (𝟙_ (Over X) ⟶ AX)), IsGrpPullback AX c.A πX φX → IsSquare φX φ₂X → RosatiFor D actX (c.P.pull φ₂X) → EtaOK D N actX ηX → ∀ (Z : Scheme.{0}) (j : Z ⟶ X), (∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ Z), x ≫ j ≫ πX ≫ t = spMap β → LieHer b actX β (x ≫ j)) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Z) (β : R →+* k), x ≫ j ≫ πX ≫ t = spMap β → GeomAt D N actX (c.P.pull φ₂X) ηX k (x ≫ j)) → ∃ (u : Obj b N ((j ≫ πX) ≫ t)) (ψ : u.A.left ⟶ AX.left) (ψ₂ : (G2 u.A).left ⟶ (G2 c.A).left), IsGrpPullback u.A AX j ψ ∧ IsSquare (ψ ≫ φX) ψ₂ ∧ LBIso u.P (c.P.pull ψ₂) ∧ (∀ a : D.O, (u.act.act a).left ≫ ψ = ψ ≫ (actX.act a).left) ∧ ∀ y, (u.eta y).left ≫ ψ = j ≫ (ηX y).left := by
  intro p _ D R _ b N _ _ h M B _ ζ S s₁ t c e he hc X πX AX _ _ φX φ₂X actX ηX hX sqX hRos hEta Z j hLie hGeom
  let A' := (Over.pullback (j ≫ πX)).obj c.A
  let φ := PullbackComparison.pφ (j ≫ πX) c.A
  let φ₂ := PullbackComparison.pφ₂ (j ≫ πX) c.A
  have pb : IsGrpPullback A' c.A (j ≫ πX) φ := PullbackComparison.isGrpPullback (j ≫ πX) c.A
  have sq : IsSquare φ φ₂ := PullbackComparison.isSquare (j ≫ πX) c.A
  have wψ : φ ≫ c.A.hom = (A'.hom ≫ j) ≫ πX := by
    rw [Category.assoc]; exact pb.1.w
  let ψ : A'.left ⟶ AX.left := hX.1.lift φ (A'.hom ≫ j) wψ
  have hψ : ψ ≫ φX = φ := hX.1.lift_fst _ _ _
  have hψh : ψ ≫ AX.hom = A'.hom ≫ j := hX.1.lift_snd _ _ _
  have pbj : IsGrpPullback A' AX j ψ := IsGrpPullback.cancel hX (by rw [hψ]; exact pb) hψh
  let ψ₂ : (G2 A').left ⟶ (G2 AX).left :=
    pullback.lift ((fst A' A').left ≫ ψ) ((snd A' A').left ≫ ψ) (by
      rw [Category.assoc, Category.assoc, hψh, ← Category.assoc, ← Category.assoc, Over.w (fst A' A'),
        Over.w (snd A' A')])
  have sqψ : IsSquare ψ ψ₂ := ⟨pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hψ₂ : ψ₂ ≫ φ₂X = φ₂ := by
    refine pullback.hom_ext (f := c.A.hom) (g := c.A.hom) ?_ ?_
    · show (ψ₂ ≫ φ₂X) ≫ (fst c.A c.A).left = φ₂ ≫ (fst c.A c.A).left
      rw [Category.assoc, sqX.1, ← Category.assoc, sqψ.1, Category.assoc, hψ, sq.1]
    · show (ψ₂ ≫ φ₂X) ≫ (snd c.A c.A).left = φ₂ ≫ (snd c.A c.A).left
      rw [Category.assoc, sqX.2, ← Category.assoc, sqψ.2, Category.assoc, hψ, sq.2]
  have hab : IsAbelianScheme A' :=
    { comm := by have := c.ab.comm; infer_instance
      smooth := by have := c.ab.smooth; show Smooth (Limits.pullback.snd _ _); infer_instance
      proper := by have := c.ab.proper; show IsProper (Limits.pullback.snd _ _); infer_instance
      geomConnected := by
        have := c.ab.geomConnected
        show GeometricallyConnected (Limits.pullback.snd _ _); infer_instance }
  obtain ⟨act', ⟨hhom, hone, hmul, hadd⟩, hact'⟩ := GlobalTheory.ActPull.exists_act_pull X Z j AX A' ψ pbj D.Oᵐᵒᵖ
    (fun a => actX.act a.unop) (fun a => actX.hom _) (by simpa using actX.one)
    (fun a b => by simpa using actX.mul b.unop a.unop) (fun a b => by simpa using actX.add a.unop b.unop)
  let actN : OActN D.O A' :=
    { act := fun c => act' (MulOpposite.op c)
      hom := fun c => hhom _
      one := by simpa using hone
      mul := fun c d => by rw [MulOpposite.op_mul]; exact hmul _ _
      add := fun c d => by rw [MulOpposite.op_add]; exact hadd _ _ }
  have hact : ∀ c, (actN.act c).left ≫ ψ = ψ ≫ (actX.act c).left := fun c => hact' (MulOpposite.op c)
  let P' : LB (G2 A').left := c.P.pull φ₂
  have hP' : P'.IsLB := pull_isLB c.isLB φ₂
  have iso : LBIso P' (c.P.pull φ₂) := PullbackComparison.gen_refl _ hP'
  have dg := SiegelPull.diag_iso sq iso
  have hPX : (c.P.pull φ₂X).IsLB := pull_isLB c.isLB φ₂X
  have H : LBIso P' ((c.P.pull φ₂X).pull ψ₂) :=
    LBIso.chartPull (chartPullSame c.P (fun _ : PUnit => φ₂) (fun _ => 𝟙 _) (fun _ => 1) φ₂
        (fun _ => (Category.comp_id _).symm))
      (chartPullLinComb c.P φ₂X (fun _ : PUnit => ψ₂) (fun _ => 𝟙 _) (fun _ => 1) φ₂
        (fun _ => by rw [hψ₂, Category.comp_id]))
      (PullbackComparison.gen_refl _ (pull_isLB c.isLB _))
  have dgX := SiegelPull.diag_iso sqψ H
  have sqL : ∀ (x' y' : G2 A' ⟶ A') (x y : G2 AX ⟶ AX), x'.left ≫ ψ = ψ₂ ≫ x.left → y'.left ≫ ψ = ψ₂ ≫ y.left →
      (lift x' y').left ≫ ψ₂ = ψ₂ ≫ (lift x y).left := fun x' y' x y hx hy =>
    (Category.id_comp _).symm.trans (SiegelPull.lift_sq sqψ (T := Over.mk (ψ₂ ≫ (G2 AX).hom)) (T' := G2 A') (𝟙 _)
      x' y' (Z := G2 AX) ψ₂ x y (by rw [Category.id_comp]; exact hx) (by rw [Category.id_comp]; exact hy))
  have rosP : RosatiFor D actN ((c.P.pull φ₂X).pull ψ₂) := fun a => LBIso.chartPull
    (chartPullLinComb (c.P.pull φ₂X) _ _ _ _ ψ₂ (fun _ => sqL _ _ _ _ (by
      rw [Over.comp_left, Over.comp_left, Category.assoc, hact, ← Category.assoc, ← sqψ.1, Category.assoc])
      (by rw [sqψ.2])))
    (chartPullLinComb (c.P.pull φ₂X) _ _ _ _ ψ₂ (fun _ => sqL _ _ _ _ (by rw [sqψ.1]) (by
      rw [Over.comp_left, Over.comp_left, Category.assoc, hact, ← Category.assoc, ← sqψ.2, Category.assoc])))
    (hRos a)
  obtain ⟨t₁, ht₁⟩ := c.rig₁
  obtain ⟨t₂, ht₂⟩ := c.rig₂
  let u : Obj b N ((j ≫ πX) ≫ t) :=
    { A := A'
      ab := hab
      act := actN
      P := P'
      isLB := hP'
      rig₁ := gen_chartPull (chartPullLinComb c.P _ _ _ _ φ (fun _ => PullbackComparison.lift_one_id (j ≫ πX) c.A)) t₁ ht₁
      rig₂ := gen_chartPull (chartPullLinComb c.P _ _ _ _ φ (fun _ => PullbackComparison.lift_id_one (j ≫ πX) c.A)) t₂ ht₂
      symm := LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull c.P _ _ rfl)
        (chartPullLinComb c.P _ _ _ _ φ₂ (fun _ => PullbackComparison.lift_swap (j ≫ πX) c.A)) c.symm
      ample := (pol_pull S Z c.A A' (j ≫ πX) φ _ _ (pull_isLB c.isLB _) (pull_isLB hP' _) c.ab pb dg).2.1 hc.1
      kerP := ⟨e, he, fun T x hx => kerBy_pull pb sq c.isLB hP' iso e hc.2 T x hx⟩
      rosati := RosatiFor.of_iso (pull_isLB hPX _) hP' (LBIso.symm H) rosP
      lie := fun R' _ β x hx v hv => by
        have hx' : x ≫ j ≫ πX ≫ t = spMap β := by simpa only [Category.assoc] using hx
        obtain ⟨e, he⟩ := GlobalTheory.LiePull.exists_pushEquiv pbj (epsPtR x) (spMap (algebraMap R' (DualNumber R')) ≫ x ≫ j)
          (Category.assoc _ _ _).symm
        obtain ⟨w, hw, hvw⟩ := lieAt_of_lieHer b (hLie R' β x hx') (e v)
          ((HTPull.isTanScal_iff pbj actX actN hact x e he _ _ v).1 hv)
        refine ⟨fun i => e.symm (w i), fun i c => (HTPull.isTanScal_iff pbj actX actN hact x e he _ _ _).2
          (by rw [e.apply_symm_apply]; exact hw i c), e.injective ?_⟩
        rw [hvw, map_list_prod, List.map_ofFn]
        simp [Function.comp_def]
      lieRank := fun k _ _ x β hx i => by
        have hx' : x ≫ j ≫ πX ≫ t = spMap β := by simpa only [Category.assoc] using hx
        exact (GlobalTheory.LiePull.lieMult_pull (𝓞 D.F) X Z AX A' j ψ (actX.toF D) (actN.toF D) pbj
          (fun c => hact _) k x (β.comp (b.t i)) D.m).2 (lieMult_of_lieHer b k (hLie k β x hx') i)
      eta := fun y => SiegelPull.secPull pbj (ηX y)
      eta_add := fun y z => SiegelPull.push_injective pbj _ (by
        rw [map_mul, push_secPull', push_secPull', push_secPull', hEta.1, MonObj.comp_mul])
      eta_lin := fun c y => SiegelPull.push_injective pbj _ (by
        rw [HTPull.push_comp pbj (hact c), push_secPull', push_secPull', hEta.2.1, Category.assoc])
      eta_ker := fun y => SiegelPull.push_injective pbj _ (by
        rw [push_secPull', hEta.2.2, map_one, MonObj.comp_one])
      geom := fun k _ _ x β hx => by
        have hx' : x ≫ j ≫ πX ≫ t = spMap β := by simpa only [Category.assoc] using hx
        obtain ⟨I, hI⟩ := hGeom k x β hx'
        let e : (Over.mk x ⟶ A') ≃* (Over.mk (x ≫ j) ⟶ AX) := MulEquiv.ofBijective (pushHom pbj (Over.mk x))
          ⟨SiegelPull.push_injective pbj _, SiegelPull.push_surjective pbj _⟩
        have ea : ∀ c g, e (g ≫ actN.act c) = e g ≫ actX.act c := fun c g => HTPull.push_comp pbj (hact c) _ g
        have ex : ∀ z, z.left = (e.symm z).left ≫ ψ := fun z =>
          (congrArg (fun q => q.left) (e.apply_symm_apply z)).symm
        refine ⟨{ ζ := I.ζ, ζ_prim := I.ζ_prim, ζ_pow := I.ζ_pow, ev := fun n y => e.symm (I.ev n y)
                  add := fun n y z => by rw [I.add, map_mul]
                  lin := fun n c y => e.injective (by rw [ea, e.apply_symm_apply, e.apply_symm_apply, I.lin])
                  ker := fun n hn hp y => by rw [map_eq_one_iff _ e.symm.injective]; exact I.ker n hn hp y
                  onto := fun n hn hp q => by
                    rw [← map_eq_one_iff e e.injective, map_pow, I.onto n hn hp (e q)]
                    exact exists_congr fun y => e.symm_apply_eq.symm
                  tower := fun n m hn hm hp y => by rw [← map_pow, I.tower n m hn hm hp]
                  isom := fun n hn hp y z => (weilIs_grpPullback_of_comm X Z AX A' j ψ _ _ (pull_isLB hPX _)
                    (pull_isLB hP' _) pbj dgX (Over.mk x) n _ _ (I.ev n y) (I.ev n z) _ (ex _) (ex _)).2
                    (I.isom n hn hp y z) }, fun y => ?_⟩
        show toUnit _ ≫ SiegelPull.secPull pbj (ηX y) = e.symm (I.ev N y)
        rw [eq_comm, e.symm_apply_eq, ← hI y]
        exact (SiegelPull.push_secPull pbj (ηX y) (Over.mk x)).symm }
  exact ⟨u, ψ, φ₂, pbj, by rw [hψ]; exact sq, iso, hact, fun y => SiegelPull.secPull_left pbj _⟩

end GlobalTheory.HTMkObj
