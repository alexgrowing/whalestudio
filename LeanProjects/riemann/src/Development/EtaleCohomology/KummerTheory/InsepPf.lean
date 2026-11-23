import Development.EtaleCohomology.KummerTheory.InjSlice

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct

namespace LateralTheory.KummerTheory.InsepPf

theorem res_comp {R : Type} [CommRing R] (F : Shv R) {W V U : Scheme.{0}} (g : W ⟶ V) (h : V ⟶ U) (x : Sec F U) :
    Sec.res (g ≫ h) x = Sec.res g (Sec.res h x) := by
  simp [Sec.res]

theorem res_id {R : Type} [CommRing R] (F : Shv R) {U : Scheme.{0}} (x : Sec F U) : Sec.res (𝟙 U) x = x := by
  simp [Sec.res]

theorem res_bij_iso {R : Type} [CommRing R] (F : Shv R) {V U : Scheme.{0}} (e : V ≅ U) :
    Function.Bijective (Sec.res (F := F) e.hom) := by
  refine Function.bijective_iff_has_inverse.2 ⟨Sec.res e.inv, fun x => ?_, fun x => ?_⟩
  · rw [← res_comp, e.inv_hom_id, res_id]
  · rw [← res_comp, e.hom_inv_id, res_id]

theorem twGen_res {q : ℕ} (i : ℤ) {V U : Scheme.{0}} (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    Sec.res g (twGen i ζ) = twGen i (Prim.map (Scheme.Γ.map g.op).hom ζ) := by
  have h := congrArg (fun f => f.hom (Submodule.Quotient.mk (Finsupp.single ζ (1 : ULift.{1} (ZMod q))) : (twF q i).obj Γ(U, ⊤)))
    ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).naturality g.op)
  simp only [ModuleCat.hom_comp] at h
  unfold twGen ofRings.sec
  refine h.symm.trans ?_
  show ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).app (op V)).hom
    (((Scheme.Γ ⋙ twF q i).map g.op).hom (Submodule.Quotient.mk (Finsupp.single ζ (1 : ULift.{1} (ZMod q))))) = _
  refine congrArg ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).app (op V)).hom ?_
  change Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map (Scheme.Γ.map g.op).hom) (Finsupp.single ζ (1 : ULift.{1} (ZMod q)))) = _
  exact congrArg _ (Finsupp.mapDomain_single (f := Prim.map (Scheme.Γ.map g.op).hom) (a := ζ) (b := (1 : ULift.{1} (ZMod q))))

theorem res_smul {R : Type} [CommRing R] (F : Shv R) {V U : Scheme.{0}} (g : V ⟶ U) (c : ULift.{1} R) (x : Sec F U) :
    Sec.res g (c • x) = c • Sec.res g x := map_smul (F.obj.map g.op).hom c x

theorem res_spec_bij (hTw : TwSec) (q : ℕ) [NeZero q] {A B : Type} [CommRing A] [CommRing B] (hA : SH A) (hB : SH B)
    (hq : IsUnit (q : A)) (φ : A →+* B) (i : ℤ) :
    Function.Bijective (Sec.res (F := tw q i) (Spec.map (CommRingCat.ofHom φ))) := by
  have hqB : IsUnit (q : B) := by simpa using hq.map φ
  obtain ⟨⟨ζ⟩, hζ⟩ := hTw q A hA hq
  have h1 := hζ i ζ
  have h2 := (hTw q B hB hqB).2 i (Prim.map (Scheme.Γ.map (Spec.map (CommRingCat.ofHom φ)).op).hom ζ)
  have e : (Sec.res (F := tw q i) (Spec.map (CommRingCat.ofHom φ))) ∘
      (fun t : ZMod q => (ULift.up t : ULift.{1} (ZMod q)) • twGen i ζ) =
      fun t : ZMod q => (ULift.up t : ULift.{1} (ZMod q)) •
        twGen i (Prim.map (Scheme.Γ.map (Spec.map (CommRingCat.ofHom φ)).op).hom ζ) := by
    funext t
    simp only [Function.comp]
    rw [res_smul, twGen_res]
    rfl
  exact (Function.Bijective.of_comp_iff _ h1).1 (by rw [e]; exact h2)

theorem res_bij (hTw : TwSec) (q : ℕ) [NeZero q] (i : ℤ) {P Q : Scheme.{0}} (m : P ⟶ Q) {A B : Type} [CommRing A]
    [CommRing B] (hA : SH A) (hB : SH B) (hq : IsUnit (q : A)) (iP : P ≅ Spec (CommRingCat.of B))
    (iQ : Q ≅ Spec (CommRingCat.of A)) : Function.Bijective (Sec.res (F := tw q i) m) := by
  set g' := iP.inv ≫ m ≫ iQ.hom
  have hm : m = iP.hom ≫ Spec.map (CommRingCat.ofHom (Spec.preimage g').hom) ≫ iQ.inv := by
    simp [g']
  have hg := res_spec_bij hTw q hA hB hq (Spec.preimage g').hom i
  have : (Sec.res (F := tw q i) m) = Sec.res iP.hom ∘ Sec.res (Spec.map (CommRingCat.ofHom (Spec.preimage g').hom)) ∘
      Sec.res (F := tw q i) iQ.inv := by
    funext x
    simp only [Function.comp]
    rw [hm, res_comp, res_comp]
  rw [this]
  exact (res_bij_iso _ iP).comp (hg.comp (res_bij_iso _ iQ.symm))

theorem sub_of_iso {R : Type} [CommRing R] (F : Shv R) (n : ℤ) {P : Scheme.{0}} {B : Type} [CommRing B]
    (e : P ≅ Spec (CommRingCat.of B)) (h : Subsingleton (H R (sp B) F n)) : Subsingleton (H R (sch.obj P) F n) := by
  refine ⟨fun x y => ?_⟩
  have hx : ∀ z : H R (sch.obj P) F n, z = pull R (sch.map e.hom) F n (pull R (sch.map e.inv) F n z) := fun z => by
    rw [← pull_comp, ← Functor.map_comp, e.hom_inv_id, CategoryTheory.Functor.map_id, pull_id]
  rw [hx x, hx y, Subsingleton.elim (pull R (sch.map e.inv) F n x) (pull R (sch.map e.inv) F n y)]

theorem bij_of_sub {G G' : Type*} [AddCommGroup G] [AddCommGroup G'] (f : G →+ G') (h : Subsingleton G)
    (h' : Subsingleton G') : Function.Bijective f :=
  ⟨fun a b _ => Subsingleton.elim a b, fun y => ⟨0, Subsingleton.elim _ _⟩⟩

theorem eqv_of (hA9 : A9) (hB2 : B2) (hTw : TwSec) (q : ℕ) [NeZero q] (i : ℤ) {P Q : Scheme.{0}} (m : P ⟶ Q)
    {A B : Type} [CommRing A] [CommRing B] (hA : SH A) (hB : SH B) (hq : IsUnit (q : A))
    (iP : P ≅ Spec (CommRingCat.of B)) (iQ : Q ≅ Spec (CommRingCat.of A)) : Eqv _ (sch.map m) (tw q i) := by
  intro n
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · exact bij_of_sub _ ((hA9 _ (tw q i)).1 _ n hn) ((hA9 _ (tw q i)).1 _ n hn)
  · obtain ⟨e, he, -⟩ := (hA9 _ (tw q i)).2
    have h0 := res_bij hTw q i m hA hB hq iP iQ
    have : (pull _ (sch.map m) (tw q i) 0 : _ → _) = e P ∘ Sec.res m ∘ (e Q).symm := by
      funext x
      simp only [Function.comp]
      rw [← he, AddEquiv.apply_symm_apply]
    rw [this]
    exact (e P).bijective.comp (h0.comp (e Q).symm.bijective)
  · exact bij_of_sub _ (sub_of_iso _ n iQ (hB2 _ A hA _ n hn)) (sub_of_iso _ n iP (hB2 _ B hB _ n hn))

theorem Insep_of (hSH : SHInsep) (hTw : TwSec) : Insep := by
  intro hA9 hB2 hB3 q _ κ K _ _ _ _ hq X p i
  have hqX : IsUnit (q : Γ(X, ⊤)) := by
    have h1 : IsUnit (q : Γ(Spec (CommRingCat.of κ), ⊤)) := by
      simpa using hq.map (Scheme.ΓSpecIso (CommRingCat.of κ)).inv.hom
    simpa using h1.map (p.appTop).hom
  refine hB3 q (pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap κ K)))) (𝟙 X) hqX i ?_
  intro A _ s hA
  let _ : Algebra κ A := (Spec.preimage (s ≫ p)).hom.toAlgebra
  have hsp : s ≫ p = Spec.map (CommRingCat.ofHom (algebraMap κ A)) := (Spec.map_preimage _).symm
  have hqA : IsUnit (q : A) := by simpa using hq.map (algebraMap κ A)
  refine eqv_of hA9 hB2 hTw q i _ hA (hSH κ K A hA) hqA ?_ (asIso (pullback.snd (𝟙 X) s))
  exact pullback.congrHom (Category.comp_id _) rfl ≪≫ pullbackSymmetry _ _ ≪≫
    pullbackRightPullbackFstIso p _ s ≪≫ pullback.congrHom hsp rfl ≪≫ pullbackSpecIso κ A K

end LateralTheory.KummerTheory.InsepPf
