import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Coords
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsStrictlySemistable
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section
namespace GlobalTheory.CompanionTheory.GrCech

section Site

variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {Fil : ℤ → IdF Φ.A}

theorem J_mul_mem (hF : IsFil Φ Fil) (r : ℕ) {T : C} {x y : Φ.A.obj T} (hx : x ∈ Φ.J.S T)
    (hy : y ∈ (Fil r).S T) : x * y ∈ (Fil ((r : ℤ) + 1)).S T := by
  have h1 : x ∈ (Fil ((1 : ℕ) : ℤ)).S T := by
    have := hF.one T
    simpa [this] using hx
  have := hF.mul 1 r T h1 hy
  have e : (((1 + r : ℕ)) : ℤ) = (r : ℤ) + 1 := by push_cast; ring
  rwa [e] at this

def mulT (Fil : ℤ → IdF Φ.A) (r : ℤ) {T : C} (u : Φ.A.obj T) : (gr Fil r).obj T →ₗ[R] (gr Fil r).obj T :=
  (LinearMap.mulLeft R (Ideal.Quotient.mk ((Fil (r + 1)).S T) u)).restrict fun x hx =>
    Ideal.mul_mem_left _ _ hx

theorem mulT_coe (r : ℤ) {T : C} (u : Φ.A.obj T) (x : (gr Fil r).obj T) :
    (show sqM (Fil r) (Fil (r + 1)) T from mulT Fil r u x).1 =
      Ideal.Quotient.mk _ u * (show sqM (Fil r) (Fil (r + 1)) T from x).1 := rfl

theorem mulT_congr (hF : IsFil Φ Fil) (r : ℕ) {T : C} {u v : Φ.A.obj T} (h : u - v ∈ Φ.J.S T)
    (x : (gr Fil r).obj T) : mulT Fil r u x = mulT Fil r v x := by
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, hy, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hx
  refine Subtype.ext ?_
  change Ideal.Quotient.mk _ u * Ideal.Quotient.mk _ y = Ideal.Quotient.mk _ v * Ideal.Quotient.mk _ y
  rw [← map_mul, ← map_mul, Ideal.Quotient.eq, ← sub_mul]
  exact J_mul_mem hF r h hy

def mulMor (hF : IsFil Φ Fil) (r : ℕ) (u : ∀ T, Φ.A.obj T)
    (hu : ∀ {T T' : C} (φ : T ⟶ T'), u T' - (Φ.A.map φ).hom (u T) ∈ Φ.J.S T') :
    CH.Mor (gr Fil r) (gr Fil r) (RingHom.id R) where
  G := 𝟭 C
  τ T := mulT Fil r (u T)
  nat {T T'} φ x := by
    have e := mulT_congr hF r (hu φ) ((gr Fil r).map φ |>.hom x)
    refine e.trans ?_
    obtain ⟨x, hx⟩ := x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine Subtype.ext ?_
    change Ideal.Quotient.mk _ ((Φ.A.map φ).hom (u T)) * Ideal.Quotient.mk _ ((Φ.A.map φ).hom y) =
      Ideal.Quotient.mk _ ((Φ.A.map φ).hom (u T * (show Φ.A.obj T from y)))
    rw [map_mul, map_mul]

end Site

end GlobalTheory.CompanionTheory.GrCech
end

noncomputable section
namespace GlobalTheory.CompanionTheory.GrCech

section Act

variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {Fil : ℤ → IdF Φ.A}

theorem pull_mk {R' : Type} [CommRing R'] {C' : Type 1} [Category.{0} C'] {F : C ⥤ ModuleCat.{0} R}
    {F' : C' ⥤ ModuleCat.{0} R'} {σ : R →+* R'} (m : CH.Mor F F' σ) (n : ℕ) (z : (CH.cx F).Z n) :
    m.pull n (Submodule.Quotient.mk z) = Submodule.Quotient.mk (m.hom.mapZ n z) := rfl

variable (hF : IsFil Φ Fil) (r : ℕ)
include hF

theorem mulMor_add {u v w : ∀ T, Φ.A.obj T} (hu hv hw) (h : ∀ T, w T - (u T + v T) ∈ Φ.J.S T) (n : ℕ) (c : CH.H (gr Fil r) n) :
    (mulMor hF r w hw).pull n c = (mulMor hF r u hu).pull n c + (mulMor hF r v hv).pull n c := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  rw [pull_mk, pull_mk, pull_mk, ← Submodule.Quotient.mk_add]
  congr 1
  refine Subtype.ext (funext fun s => ?_)
  refine (mulT_congr hF r (h _) (z.1 s)).trans ?_
  refine Subtype.ext ?_
  change Ideal.Quotient.mk _ (u _ + v _) * _ = Ideal.Quotient.mk _ (u _) * _ + Ideal.Quotient.mk _ (v _) * _
  rw [map_add, add_mul]
  rfl

theorem mulMor_mul {u v w : ∀ T, Φ.A.obj T} (hu hv hw) (h : ∀ T, w T - u T * v T ∈ Φ.J.S T) (n : ℕ) (c : CH.H (gr Fil r) n) :
    (mulMor hF r w hw).pull n c = (mulMor hF r u hu).pull n ((mulMor hF r v hv).pull n c) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  rw [pull_mk, pull_mk, pull_mk]
  congr 1
  refine Subtype.ext (funext fun s => ?_)
  refine (mulT_congr hF r (h _) (z.1 s)).trans ?_
  refine Subtype.ext ?_
  change Ideal.Quotient.mk _ (u _ * v _) * _ = Ideal.Quotient.mk _ (u _) * (Ideal.Quotient.mk _ (v _) * _)
  rw [map_mul, mul_assoc]
  rfl

theorem mulMor_smul {u : ∀ T, Φ.A.obj T} (hu) (a : R) (h : ∀ T, u T - algebraMap R _ a ∈ Φ.J.S T) (n : ℕ) (c : CH.H (gr Fil r) n) :
    (mulMor hF r u hu).pull n c = a • c := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  rw [pull_mk, ← Submodule.Quotient.mk_smul]
  congr 1
  refine Subtype.ext (funext fun s => ?_)
  refine (mulT_congr hF r (h _) (z.1 s)).trans ?_
  refine Subtype.ext ?_
  exact (Algebra.smul_def a (show sqM (Fil r) (Fil ((r : ℤ) + 1)) _ from z.1 s).1).symm

end Act

section Thickenings

variable {O : Type} [CommRing O] {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ}
  {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I}

theorem ev_map {W : X.Opens} {T T' : Thick (nlFun γ p X q κ)} (φ : T ⟶ T') (h : InU W T) (h' : InU W T')
    (f : Γ(X, W)) : ev T' h' f = Ideal.quotientMap T'.J φ.φ φ.hle (ev T h f) := by
  have e : pt T' = Spec.map (CommRingCat.ofHom (Ideal.quotientMap T'.J φ.φ φ.hle)) ≫ pt T := by
    have := φ.pt
    unfold pt
    rw [← this]
    rfl
  have key : ∀ (y : Spec (CommRingCat.of (T'.B ⧸ T'.J)) ⟶ X) (hy : y = Spec.map (CommRingCat.ofHom (Ideal.quotientMap T'.J φ.φ φ.hle)) ≫ pt T)
      (h'' : ⊤ ≤ y ⁻¹ᵁ W), GlobalTheory.Cris.evalAt y W h'' f = Ideal.quotientMap T'.J φ.φ φ.hle (ev T h f) := by
    intro y hy h''
    subst hy
    exact GlobalTheory.LogCris.evalAt_map _ (pt T) h h'' f
  exact key _ e h'

def evLift {Q : ObjectProperty (Thick (nlFun γ p X q κ))} {W : X.Opens} (hQ : ∀ T, Q T → InU W T) (f : Γ(X, W))
    (T : Q.FullSubcategory) : (sP Q).A.obj T :=
  Function.surjInv (Ideal.Quotient.mk_surjective (I := T.obj.J)) (ev T.obj (hQ _ T.property) f)

theorem mk_evLift {Q : ObjectProperty (Thick (nlFun γ p X q κ))} {W : X.Opens} (hQ : ∀ T, Q T → InU W T) (f : Γ(X, W))
    (T : Q.FullSubcategory) : Ideal.Quotient.mk T.obj.J (evLift hQ f T) = ev T.obj (hQ _ T.property) f :=
  Function.surjInv_eq _ _

theorem sub_mem_of_mk {T : Thick (nlFun γ p X q κ)} {x y : T.B} (h : Ideal.Quotient.mk T.J x = Ideal.Quotient.mk T.J y) :
    x - y ∈ T.J := Ideal.Quotient.eq.1 h

theorem evLift_nat {Q : ObjectProperty (Thick (nlFun γ p X q κ))} {W : X.Opens} (hQ : ∀ T, Q T → InU W T) (f : Γ(X, W))
    {T T' : Q.FullSubcategory} (φ : T ⟶ T') :
    evLift hQ f T' - ((sP Q).A.map φ).hom (evLift hQ f T) ∈ (sP Q).J.S T' := by
  refine sub_mem_of_mk (T := T'.obj) ?_
  rw [mk_evLift, ev_map φ.hom (hQ _ T.property) (hQ _ T'.property), ← mk_evLift hQ f T]
  rfl

abbrev grF (L : (nlBase R I γ p).Fun) (r : ℕ) : Thick L ⥤ ModuleCat.{0} R :=
  sq (thFil L r) (thFil L ((r : ℤ) + 1))

def fAct {Q : ObjectProperty (Thick (nlFun γ p X q κ))} (hF : IsFil (sP Q) (sFil Q)) {W : X.Opens}
    (hQ : ∀ T, Q T → InU W T) (r : ℕ) (f : Γ(X, W)) :
    HU (grF (nlFun γ p X q κ) r) Q r →ₗ[R] HU (grF (nlFun γ p X q κ) r) Q r :=
  (mulMor hF r (evLift hQ f) (evLift_nat hQ f)).pull r

end Thickenings

end GlobalTheory.CompanionTheory.GrCech
end

noncomputable section
namespace GlobalTheory.CompanionTheory.GrCech

section ThAct

variable {O : Type} [CommRing O] {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ}
  {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I}
  {Q : ObjectProperty (Thick (nlFun γ p X q κ))} (hF : IsFil (sP Q) (sFil Q)) {W : X.Opens}
  (hQ : ∀ T, Q T → InU W T) (r : ℕ)

theorem fAct_add (f g : Γ(X, W)) (c : HU (grF (nlFun γ p X q κ) r) Q r) :
    fAct hF hQ r (f + g) c = fAct hF hQ r f c + fAct hF hQ r g c := by
  refine mulMor_add hF r _ _ _ (fun T => sub_mem_of_mk (T := T.obj) ?_) r c
  rw [mk_evLift, map_add (Ideal.Quotient.mk T.obj.J), mk_evLift, mk_evLift, map_add]

theorem fAct_mul (f g : Γ(X, W)) (c : HU (grF (nlFun γ p X q κ) r) Q r) :
    fAct hF hQ r (f * g) c = fAct hF hQ r f (fAct hF hQ r g c) := by
  refine mulMor_mul hF r _ _ _ (fun T => sub_mem_of_mk (T := T.obj) ?_) r c
  rw [mk_evLift, map_mul (Ideal.Quotient.mk T.obj.J), mk_evLift, mk_evLift, map_mul]

theorem fAct_one (c : HU (grF (nlFun γ p X q κ) r) Q r) : fAct hF hQ r 1 c = c := by
  refine (mulMor_smul hF r _ (1 : R) (fun T => sub_mem_of_mk (T := T.obj) ?_) r c).trans (one_smul _ _)
  rw [mk_evLift, map_one, map_one (algebraMap R _)]
  exact (map_one _).symm

def fHom : Γ(X, W) →+* AddMonoid.End (HU (grF (nlFun γ p X q κ) r) Q r) :=
  RingHom.mk' { toFun := fun f => (fAct hF hQ r f).toAddMonoidHom
                map_one' := AddMonoidHom.ext fun c => fAct_one hF hQ r c
                map_mul' := fun f g => AddMonoidHom.ext fun c => fAct_mul hF hQ r f g c }
    fun f g => AddMonoidHom.ext fun c => fAct_add hF hQ r f g c

theorem fHom_apply (f : Γ(X, W)) (c : HU (grF (nlFun γ p X q κ) r) Q r) : fHom hF hQ r f c = fAct hF hQ r f c := rfl

theorem ev_rs {W' : X.Opens} (hW : W' ≤ W) (T : Thick (nlFun γ p X q κ)) (h : InU W T) (h' : InU W' T) (f : Γ(X, W)) :
    ev T h' (rs hW f) = ev T h f :=
  GlobalTheory.LogCris.evalAt_res (pt T) hW h h' f

theorem res_fAct {Q' : ObjectProperty (Thick (nlFun γ p X q κ))} (hF' : IsFil (sP Q') (sFil Q')) {W' : X.Opens}
    (hQ' : ∀ T, Q' T → InU W' T) (hW : W' ≤ W) (hle : Q' ≤ Q) (f : Γ(X, W)) (c : HU (grF (nlFun γ p X q κ) r) Q r) :
    (resU (grF (nlFun γ p X q κ) r) hle).pull r (fAct hF hQ r f c) =
      fAct hF' hQ' r (rs hW f) ((resU (grF (nlFun γ p X q κ) r) hle).pull r c) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  change Submodule.Quotient.mk ((resU (grF (nlFun γ p X q κ) r) hle).hom.mapZ r ((mulMor hF r (evLift hQ f) (evLift_nat hQ f)).hom.mapZ r z)) =
    Submodule.Quotient.mk ((mulMor hF' r (evLift hQ' (rs hW f)) (evLift_nat hQ' (rs hW f))).hom.mapZ r ((resU (grF (nlFun γ p X q κ) r) hle).hom.mapZ r z))
  congr 1
  refine Subtype.ext (funext fun s => ?_)
  refine Eq.symm (((mulT_congr hF' r (T := s.obj (Fin.last r)) (u := evLift hQ' (rs hW f) _) (v := evLift hQ f ((ObjectProperty.ιOfLE hle).obj (s.obj (Fin.last r)))) ?_ _)).trans ?_)
  · refine sub_mem_of_mk (T := (s.obj (Fin.last r)).obj) ?_
    rw [mk_evLift]
    exact (ev_rs hW _ (hQ _ (hle _ (s.obj (Fin.last r)).property)) _ _).trans (mk_evLift hQ f ((ObjectProperty.ιOfLE hle).obj (s.obj (Fin.last r)))).symm
  · rfl

end ThAct

end GlobalTheory.CompanionTheory.GrCech
end

noncomputable section
namespace GlobalTheory.CompanionTheory.GrCech

section Sec

variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {Fil : ℤ → IdF Φ.A}

theorem sec_nat (hF : IsFil Φ Fil) {d : ℕ} (E : Frame Φ d) (σ : ∀ T : C, E.D ⟶ T) (hc : E.GrConst Fil)
    (x : Φ.A.obj E.D) {T T' : C} (φ : T ⟶ T') :
    (Φ.A.map (σ T')).hom x - (Φ.A.map φ).hom ((Φ.A.map (σ T)).hom x) ∈ Φ.J.S T' := by
  have h0 : x ∈ (Fil ((0 : ℕ) : ℤ)).S E.D := by
    rw [hF.top _ (by simp)]; trivial
  have h1 := hc 0 (σ T') (σ T ≫ φ) h0
  have e : (((0 : ℕ) : ℤ) + 1) = 1 := by simp
  rw [e, hF.one, Φ.A.map_comp] at h1
  exact h1

def secMor (hF : IsFil Φ Fil) (r : ℕ) {d : ℕ} (E : Frame Φ d) (σ : ∀ T : C, E.D ⟶ T) (hc : E.GrConst Fil)
    (x : Φ.A.obj E.D) : CH.Mor (gr Fil r) (gr Fil r) (RingHom.id R) :=
  mulMor hF r (fun T => (Φ.A.map (σ T)).hom x) (sec_nat hF E σ hc x)

end Sec

section Res

variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C]

theorem res_res (F : C ⥤ ModuleCat.{0} R) {U V W : ObjectProperty C} (h₁ : V ≤ U) (h₂ : W ≤ V) (n : ℕ) (c : HU F U n) :
    (resU F h₂).pull n ((resU F h₁).pull n c) = (resU F (h₂.trans h₁)).pull n c := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  rfl

end Res

section Str

variable {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}
  {Q : ObjectProperty (Thick (nlFun (dividedPowersBot O) 0 X q (Ideal.Quotient.mk ⊥)))} (hF : IsFil (sP Q) (sFil Q)) {W : X.Opens}
  (hQ : ∀ T, Q T → InU W T) (r : ℕ)

theorem fAct_str (a : O) (c : HU (grF (nlFun (dividedPowersBot O) 0 X q (Ideal.Quotient.mk ⊥)) r) Q r) :
    fAct hF hQ r (strV q W a) c = a • c := by
  refine mulMor_smul hF r _ a (fun T => sub_mem_of_mk (T := T.obj) ?_) r c
  rw [mk_evLift]
  have e := GlobalTheory.LogCris.evalAt_base q (Ideal.Quotient.mk ⊥) (T.obj.y.1.1) (T.obj.y.1.2) T.obj.y.2 (hQ _ T.property) a
  exact e.trans (T.obj.w a)

end Str

end GlobalTheory.CompanionTheory.GrCech
end
