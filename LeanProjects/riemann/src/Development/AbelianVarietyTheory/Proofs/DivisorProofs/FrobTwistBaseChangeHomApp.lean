import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToBaseChangePtsBijective
import Development.AbelianVarietyTheory.Definitions.Divisors.PrismaticDieudonnePerfdIff
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFrobGBaseChange

set_option autoImplicit false

noncomputable section

open TensorProduct Coalgebra Bialgebra WithConv CategoryTheory

namespace GlobalTheory

namespace PDiv

section Over

variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] [Algebra R R']
  {A A'' : Type} [CommRing A] [Bialgebra R A] [CommRing A''] [Bialgebra R'' A'']

def SemiBialgHom.liftOver {ρ : R →+* R''} (f : SemiBialgHom ρ A A'') (τ : R' →+* R'')
    (h : ∀ r, ρ r = τ (algebraMap R R' r)) : SemiBialgHom τ (R' ⊗[R] A) A'' :=
  letI : Algebra R A'' := ((algebraMap R'' A'').comp ρ).toAlgebra
  let g : R' ⊗[R] A →ₐ[R] A'' := Algebra.TensorProduct.lift
    { (algebraMap R'' A'').comp τ with commutes' := fun r => congrArg (algebraMap R'' A'') (h r).symm }
    { f.toRingHom with commutes' := f.map_algebraMap } fun _ _ => .all _ _
  have hg : ∀ r a, g (r ⊗ₜ a) = τ r • f a := fun r a => (Algebra.smul_def (τ r) (f a)).symm
  have hs : ∀ (r : R') x, g (r • x) = τ r • g x := fun r x => by
    induction x with
    | zero => simp
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]
    | tmul s a => rw [smul_tmul', hg, hg, smul_eq_mul, map_mul, mul_smul]
  { toRingHom := g
    smul_map := hs
    counit_map := fun x => by
      change counit (g x) = _
      induction x with
      | zero => simp
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul r a =>
        rw [hg, map_smul, f.counit_map, TensorProduct.counit_tmul, h]
        simp [Algebra.smul_def, mul_comm]
    comul_map := fun x => by
      change comul (g x) = _
      induction x with
      | zero => simp
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul r a =>
        rw [← mul_one r, ← smul_eq_mul, ← smul_tmul', hs, map_smul, map_smul, map_smulₛₗ, hg, map_one,
          one_smul]
        congr 1
        change _ = TensorProduct.map _ _ (comul (toBaseChange R R' A a))
        rw [← SemiBialgHom.two_comul, ← SemiBialgHom.two_comul]
        generalize comul (R := R) a = c
        induction c with
        | zero => simp
        | add x y hx hy => simp only [map_add, hx, hy]
        | tmul a b => simp [hg] }

@[simp] theorem SemiBialgHom.liftOver_tmul {ρ : R →+* R''} (f : SemiBialgHom ρ A A'')
    (τ : R' →+* R'') (h : ∀ r, ρ r = τ (algebraMap R R' r)) (r : R') (a : A) :
    f.liftOver τ h (r ⊗ₜ a) = τ r • f a := (Algebra.smul_def (τ r) (f a)).symm

end Over

section Frobenius

variable {p : ℕ} [hp : Fact p.Prime] {R : Type} [CommRing R]

abbrev frobRing (h : (p : R) = 0) : R →+* R := SS.FrobField.powHom R p 1 hp.out h

@[simp] theorem frobRing_apply (h : (p : R) = 0) (r : R) : frobRing h r = r ^ p :=
  congrArg (r ^ ·) (pow_one p)

omit hp in

theorem natCast_eq_zero_of_algebra (h : (p : R) = 0) (A : Type) [CommRing A] [Algebra R A] :
    (p : A) = 0 := by
  rw [← map_natCast (algebraMap R A), h, map_zero]

def frobBialg (h : (p : R) = 0) (A : Type) [CommRing A] [Bialgebra R A] :
    SemiBialgHom (frobRing h) A A where
  toRingHom := frobRing (natCast_eq_zero_of_algebra h A)
  smul_map r a := by simp only [frobRing_apply, smul_pow]
  counit_map a := by simp only [frobRing_apply, counit_pow]
  comul_map a := by
    rw [frobRing_apply, comul_pow, ← frobRing_apply (natCast_eq_zero_of_algebra h (A ⊗[R] A))]
    generalize comul (R := R) a = c
    induction c with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a b => simp [Algebra.TensorProduct.tmul_pow]

@[simp] theorem frobBialg_apply (h : (p : R) = 0) {A : Type} [CommRing A] [Bialgebra R A] (a : A) :
    frobBialg h A a = a ^ p := frobRing_apply (natCast_eq_zero_of_algebra h A) a

end Frobenius

end PDiv

namespace PDivGroup

open PDiv

section Over

variable {p : ℕ} {O O' O'' : Type} [CommRing O] [CommRing O'] [CommRing O''] [Algebra O O']
  {G : PDivGroup p O}

def SemiHom.liftOver {G'' : PDivGroup p O''} {ρ : O →+* O''} (s : SemiHom ρ G'' G) (τ : O' →+* O'')
    (h : ∀ r, ρ r = τ (algebraMap O O' r)) : SemiHom τ G'' (G.baseChange O') :=
  ⟨fun n => (s.app n).liftOver τ h, fun n x => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul r a => simp [s.res_app]⟩

@[simp] theorem SemiHom.liftOver_app {G'' : PDivGroup p O''} {ρ : O →+* O''} (s : SemiHom ρ G'' G)
    (τ : O' →+* O'') (h : ∀ r, ρ r = τ (algebraMap O O' r)) (n : ℕ) (r : O') (a : G.A n) :
    (s.liftOver τ h).app n (r ⊗ₜ a) = τ r • s.app n a := (s.app n).liftOver_tmul τ h r a

variable (O') in

theorem baseChange_induction (n : ℕ) {P : (G.baseChange O').A n → Prop} (h0 : P 0)
    (h1 : ∀ (r : O') a, P (r • (G.toBase O').app n a)) (h2 : ∀ x y, P x → P y → P (x + y))
    (x : (G.baseChange O').A n) : P x := by
  induction x using TensorProduct.induction_on with
  | zero => exact h0
  | add x y hx hy => exact h2 x y hx hy
  | tmul r a =>
    have e : r • (G.toBase O').app n a = r ⊗ₜ[O] a := by rw [toBase_app, smul_tmul', smul_eq_mul, mul_one]
    exact e ▸ h1 r a

variable [Fact p.Prime]

theorem dualBaseChange_toBase (n : ℕ) (χ : CartierDual O (G.A n)) (a : G.A n) :
    ((PerfdLat.dualBaseChange O' G).hom.app n ((G.dual.toBase O').app n χ)).ofConv
      ((G.toBase O').app n a) = algebraMap O O' (χ a) := by
  change CartierDual.baseChange O O' (G.A n) (1 ⊗ₜ χ) (1 ⊗ₜ a) = _
  rw [CartierDual.baseChange_tmul_tmul, one_mul, Algebra.algebraMap_eq_smul_one]

theorem baseChange_ext_dual (n : ℕ) {x y : (G.baseChange O').A n}
    (h : ∀ χ : CartierDual O (G.A n),
      ((PerfdLat.dualBaseChange O' G).hom.app n ((G.dual.toBase O').app n χ)).ofConv x =
      ((PerfdLat.dualBaseChange O' G).hom.app n ((G.dual.toBase O').app n χ)).ofConv y) : x = y := by
  refine CartierDual.eq_of_forall_apply (R := O') fun φ => ?_
  obtain ⟨z, rfl⟩ : ∃ z, (PerfdLat.dualBaseChange O' G).hom.app n z = φ :=
    (CartierDual.baseChange O O' (G.A n)).surjective φ
  induction z using baseChange_induction O' (G := G.dual) n with
  | h0 => simp
  | h1 r χ => rw [map_smul, ofConv_smul, LinearMap.smul_apply, LinearMap.smul_apply, h]
  | h2 z w hz hw => rw [map_add, ofConv_add, LinearMap.add_apply, LinearMap.add_apply, hz, hw]

end Over

variable {p : ℕ} [Fact p.Prime] {R S : Type} [CommRing R] [CommRing S] (h : (p : R) = 0)
  (G : PDivGroup p R) {H K : PDivGroup p R}

def absFrob : SemiHom (frobRing h) G G :=
  ⟨fun n => frobBialg h (G.A n), fun n a => by simp only [frobBialg_apply, map_pow]⟩

@[simp] theorem absFrob_app (n : ℕ) (a : G.A n) : (absFrob h G).app n a = a ^ p :=
  frobBialg_apply h a

def frobTwist : PDivGroup p R :=
  letI := (frobRing h).toAlgebra
  G.baseChange R

@[simp] theorem frobTwist_height : (frobTwist h G).height = G.height := rfl

def frobProj : SemiHom (frobRing h) (frobTwist h G) G :=
  letI := (frobRing h).toAlgebra
  G.toBase R

variable {G} in

def frobLift (s : SemiHom (frobRing h) H G) : H ⟶ frobTwist h G :=
  letI := (frobRing h).toAlgebra
  SemiHom.lift (O := R) (O' := R) s

variable {G} in

@[simp] theorem frobLift_app_frobProj (s : SemiHom (frobRing h) H G) (n : ℕ) (a : G.A n) :
    (frobLift h s).app n ((frobProj h G).app n a) = s.app n a :=
  letI := (frobRing h).toAlgebra
  (SemiHom.lift_app (O := R) (O' := R) s n 1 a).trans (one_smul _ _)

def relFrob : G ⟶ frobTwist h G := frobLift h (absFrob h G)

def frobTwistDual : (frobTwist h G).dual ≅ frobTwist h G.dual :=
  letI := (frobRing h).toAlgebra
  PerfdLat.dualBaseChange R G

def verschiebung : frobTwist h G ⟶ G :=
  (frobTwist h G).bidual.hom ≫
    dualHom _ _ (relFrob h G.dual ≫ (frobTwistDual h G).inv) ≫ G.bidual.inv

variable {G}

def frobTwistMap (f : G ⟶ H) : frobTwist h G ⟶ frobTwist h H :=
  letI := (frobRing h).toAlgebra
  baseChangeMap R f

@[simp] theorem frobTwistMap_app_frobProj (f : G ⟶ H) (n : ℕ) (a : H.A n) :
    (frobTwistMap h f).app n ((frobProj h H).app n a) = (frobProj h G).app n (f.app n a) := rfl

theorem frobTwist_induction (n : ℕ) {P : (frobTwist h G).A n → Prop} (h0 : P 0)
    (h1 : ∀ (r : R) a, P (r • (frobProj h G).app n a)) (h2 : ∀ x y, P x → P y → P (x + y))
    (x : (frobTwist h G).A n) : P x :=
  letI := (frobRing h).toAlgebra
  baseChange_induction R n h0 h1 h2 x

theorem frobTwist_hom_ext {f g : H ⟶ frobTwist h G}
    (e : ∀ n a, f.app n ((frobProj h G).app n a) = g.app n ((frobProj h G).app n a)) : f = g :=
  letI := (frobRing h).toAlgebra
  baseChange_hom_ext e

@[simp] theorem frobTwistMap_id : frobTwistMap h (𝟙 G) = 𝟙 _ := frobTwist_hom_ext h fun _ _ => rfl

theorem frobTwistMap_comp (f : G ⟶ H) (g : H ⟶ K) :
    frobTwistMap h (f ≫ g) = frobTwistMap h f ≫ frobTwistMap h g :=
  frobTwist_hom_ext h fun _ _ => rfl

theorem frobTwistMap_add (f g : G ⟶ H) :
    frobTwistMap h (f + g) = frobTwistMap h f + frobTwistMap h g :=
  letI := (frobRing h).toAlgebra
  baseChangeMap_add R f g

@[simp] theorem relFrob_app_frobProj (n : ℕ) (a : G.A n) :
    (relFrob h G).app n ((frobProj h G).app n a) = a ^ p :=
  (frobLift_app_frobProj h _ n a).trans (absFrob_app h G n a)

theorem frobTwistDual_frobProj (n : ℕ) (χ : CartierDual R (G.A n)) (a : G.A n) :
    ((frobTwistDual h G).hom.app n ((frobProj h G.dual).app n χ)).ofConv
      ((frobProj h G).app n a) = χ a ^ p :=
  letI := (frobRing h).toAlgebra
  (dualBaseChange_toBase (O' := R) n χ a).trans (frobRing_apply h _)

theorem frobTwist_ext_dual (n : ℕ) {x y : (frobTwist h G).A n}
    (e : ∀ χ : CartierDual R (G.A n),
      ((frobTwistDual h G).hom.app n ((frobProj h G.dual).app n χ)).ofConv x =
      ((frobTwistDual h G).hom.app n ((frobProj h G.dual).app n χ)).ofConv y) : x = y :=
  letI := (frobRing h).toAlgebra
  baseChange_ext_dual (O' := R) n e

theorem frobTwistDual_verschiebung (n : ℕ) (χ : CartierDual R (G.A n)) (a : G.A n) :
    ((frobTwistDual h G).hom.app n ((frobProj h G.dual).app n χ)).ofConv
      ((verschiebung h G).app n a) = (χ ^ p) a := by
  refine (CartierDual.apply_bidual_symm _ _).trans ?_
  change ((relFrob h G.dual).app n (((frobTwistDual h G).inv ≫ (frobTwistDual h G).hom).app n
    ((frobProj h G.dual).app n χ))).ofConv a = _
  rw [Iso.inv_hom_id]
  exact congrArg (fun φ : CartierDual R (G.A n) => φ a) (relFrob_app_frobProj h (G := G.dual) n χ)

def SemiHom.frobTwist (h' : (p : S) = 0) {σ : R →+* S} {G' : PDivGroup p S} (s : SemiHom σ G' G) :
    SemiHom σ (frobTwist h' G') (frobTwist h G) :=
  letI := (frobRing h).toAlgebra
  ((frobProj h' G').comp s).liftOver σ fun r =>
    (frobRing_apply h' _).trans ((map_pow σ r p).symm.trans (congrArg σ (frobRing_apply h r).symm))

@[simp] theorem SemiHom.frobTwist_app_frobProj (h' : (p : S) = 0) {σ : R →+* S}
    {G' : PDivGroup p S} (s : SemiHom σ G' G) (n : ℕ) (a : G.A n) :
    (s.frobTwist h h').app n ((frobProj h G).app n a) = (frobProj h' G').app n (s.app n a) :=
  letI := (frobRing h).toAlgebra
  (SemiHom.liftOver_app ((frobProj h' G').comp s) σ _ n 1 a).trans
    (by rw [map_one, one_smul, SemiHom.comp_app])

section BaseChange

variable (h' : (p : S) = 0) [Algebra R S] (G)

def frobProjBaseChange :
    SemiHom (frobRing h') ((frobTwist h G).baseChange S) (G.baseChange S) :=
  (((frobTwist h G).toBase S).comp (frobProj h G)).liftOver (frobRing h') fun r => by
    simp only [RingHom.comp_apply, frobRing_apply, map_pow]

def frobTwistBaseChange : frobTwist h' (G.baseChange S) ≅ (frobTwist h G).baseChange S where
  hom := ((G.toBase S).frobTwist h h').lift
  inv := frobLift h' (frobProjBaseChange h G h')
  hom_inv_id := frobTwist_hom_ext h' fun n x => by
    refine (congrArg (((G.toBase S).frobTwist h h').lift.app n)
      (frobLift_app_frobProj h' (frobProjBaseChange h G h') n x)).trans ?_
    change _ = (frobProj h' (G.baseChange S)).app n x
    induction x using baseChange_induction S (G := G) n with
    | h0 => simp only [map_zero]
    | h2 x y hx hy => simp only [map_add, hx, hy]
    | h1 r a =>
      rw [SemiBialgHom.smul_map, SemiBialgHom.smul_map, map_smul]
      congr 1
      refine (congrArg _ (SemiHom.liftOver_app _ _ _ n 1 a)).trans ?_
      rw [map_one, one_smul]
      exact (SemiHom.lift_app _ n 1 _).trans ((one_smul _ _).trans
        (SemiHom.frobTwist_app_frobProj h h' _ n a))
  inv_hom_id := baseChange_hom_ext fun n x => by
    refine (congrArg ((frobLift h' (frobProjBaseChange h G h')).app n)
      ((SemiHom.lift_app ((G.toBase S).frobTwist h h') n 1 x).trans (one_smul _ _))).trans ?_
    change _ = ((frobTwist h G).toBase S).app n x
    induction x using frobTwist_induction h (G := G) n with
    | h0 => simp only [map_zero]
    | h2 x y hx hy => simp only [map_add, hx, hy]
    | h1 r a =>
      rw [SemiBialgHom.smul_map, SemiBialgHom.smul_map, SemiHom.frobTwist_app_frobProj, map_smul,
        frobLift_app_frobProj]
      exact congrArg _ ((SemiHom.liftOver_app _ _ _ n 1 a).trans (by rw [map_one, one_smul]; rfl))

theorem frobTwistBaseChange_hom_app (n : ℕ) (x : (frobTwist h G).A n) :
    (frobTwistBaseChange h G h').hom.app n (((frobTwist h G).toBase S).app n x) =
      ((G.toBase S).frobTwist h h').app n x :=
  (SemiHom.lift_app _ n 1 x).trans (one_smul _ _)

end BaseChange

end PDivGroup

end GlobalTheory
