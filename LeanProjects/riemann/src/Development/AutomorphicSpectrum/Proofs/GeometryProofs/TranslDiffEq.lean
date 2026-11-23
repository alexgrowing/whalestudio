import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ToFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Coc

section Thick

variable {X0 : Scheme.{0}} (G : Over X0) {k : Type} [Field k] (x : Sp k ⟶ X0)

abbrev Tm (m : ℕ) : Over X0 := overAt x (Jet k Unit m)

abbrev Ym (m : ℕ) : Scheme.{0} := (Tm x m ⊗ G).left

def prZ (m : ℕ) : Ym G x m ⟶ pullback G.hom x :=
  pullback.lift (snd (Tm x m) G).left ((fst (Tm x m) G).left ≫ spMap (algebraMap k (Jet k Unit m))) (by
    have h₁ := Over.w (snd (Tm x m) G)
    have h₂ := Over.w (fst (Tm x m) G)
    rw [h₁, Category.assoc]
    exact h₂.symm)

abbrev FinalForm : Over X0 := Over.mk (pullback.snd G.hom x ≫ x)

def secZ (m : ℕ) : pullback G.hom x ⟶ Ym G x m :=
  (lift (Over.homMk (pullback.snd G.hom x ≫ spMap ((jetAug : Jet k Unit m →ₐ[k] k) : Jet k Unit m →+* k)) (by
      dsimp
      rw [Category.assoc, ← Category.assoc (spMap _), spMap_comp_alg]
      simp [spMap]) : FinalForm G x ⟶ Tm x m)
    (Over.homMk (pullback.fst G.hom x) pullback.condition : FinalForm G x ⟶ G)).left

def dlt (m : ℕ) : Γ(Ym G x m, ⊤) :=
  ((fst (Tm x m) G).left.appTop).hom (toΓ _ (Ideal.Quotient.mk _ (MvPolynomial.X ())))

def dltOn (m : ℕ) (V : (Ym G x m).Opens) : Γ(Ym G x m, V) :=
  ((Ym G x m).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom (dlt G x m)

def trY (p : ℕ) (hp : 1 ≤ p) : Ym G x 1 ⟶ Ym G x p := (homAt x (toFirst k p hp) ▷ G).left

def pb (m : ℕ) : Ym G x m ⟶ G.left := (snd (Tm x m) G).left

def pa [GrpObj G] {m : ℕ} (y : Tm x m ⟶ G) : Ym G x m ⟶ G.left :=
  (lift (fst (Tm x m) G ≫ y) (snd (Tm x m) G) ≫ μ[G]).left

end Thick

section Ring

variable {k : Type} [Field k] (B : Type) [CommRing B] [Algebra k B] (p : ℕ)

def dQ : Jet B Unit p := Ideal.Quotient.mk _ (MvPolynomial.X ())

theorem dQ_pow : dQ B p ^ (p + 1) = 0 := by
  rw [dQ, ← map_pow]
  exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.pow_mem_pow (X_mem_orig _) _)

def inL : Jet k Unit p →ₐ[k] Jet B Unit p :=
  liftJet (MvPolynomial.aeval fun _ => dQ B p) (by
    have : Ideal.span (Set.range fun i : Unit =>
        (MvPolynomial.aeval (R := k) fun _ => dQ B p) (MvPolynomial.X i : MvPolynomial Unit k)) =
        Ideal.span {dQ B p} := by
      congr 1
      ext a
      simp
    rw [this, Ideal.span_singleton_pow, dQ_pow]
    simp)

def inR : B →ₐ[k] Jet B Unit p := IsScalarTower.toAlgHom k B (Jet B Unit p)

end Ring

section Test

variable {X0 : Scheme.{0}} (G : Over X0) [GrpObj G] {k : Type} [Field k] (x : Sp k ⟶ X0)
variable {B : Type} [CommRing B] [Algebra k B]

def xkZ (z : overAt x B ⟶ G) : Sp B ⟶ pullback G.hom x :=
  pullback.lift z.left (spMap (algebraMap k B)) (Over.w z)

def rQ (p : ℕ) (z : overAt x B ⟶ G) : Sp (Jet B Unit p) ⟶ Ym G x p :=
  (lift (homAt x (inL (k := k) B p)) (homAt x (inR (k := k) B p) ≫ z) : overAt x (Jet B Unit p) ⟶ Tm x p ⊗ G).left

end Test

section Ser

variable {k : Type} [CommRing k] {d : ℕ}

def dSer (g : Germ.PS k 2 d) (u : Fin d → k) : MvPowerSeries (Fin 1 × Fin d) k :=
  ∑ i, MvPowerSeries.C (u i) * Germ.ev (n := 1) ![0, Germ.pt k d 0] (MvPowerSeries.pderiv k ((0 : Fin 2), i) g)

end Ser

end GlobalTheory.CompanionTheory.Ar.Coc

namespace GlobalTheory.CompanionTheory.Ar.Coc

section
variable {X0 : Scheme.{0}} (G : Over X0) {k : Type} [Field k] (x : Sp k ⟶ X0)

@[reassoc (attr := simp)]
theorem prZ_fst (m : ℕ) : prZ G x m ≫ pullback.fst G.hom x = pb G x m := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem prZ_snd (m : ℕ) : prZ G x m ≫ pullback.snd G.hom x =
    (fst (Tm x m) G).left ≫ spMap (algebraMap k (Jet k Unit m)) := pullback.lift_snd _ _ _

theorem secZ_snd (m : ℕ) : secZ G x m ≫ (snd (Tm x m) G).left = pullback.fst G.hom x := by
  rw [secZ, ← Over.comp_left, lift_snd]; rfl

theorem secZ_fst (m : ℕ) : secZ G x m ≫ (fst (Tm x m) G).left =
    pullback.snd G.hom x ≫ spMap ((jetAug : Jet k Unit m →ₐ[k] k) : Jet k Unit m →+* k) := by
  rw [secZ, ← Over.comp_left, lift_fst]; rfl

theorem secZ_prZ (m : ℕ) : secZ G x m ≫ prZ G x m = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, prZ_fst, Category.id_comp]; exact secZ_snd G x m
  · rw [Category.assoc, prZ_snd, Category.id_comp, ← Category.assoc, secZ_fst, Category.assoc]
    have := spMap_comp_alg (S := k) (A := Jet k Unit m) (B := k) jetAug
    erw [this]
    simp [spMap]

theorem trY_prZ (p : ℕ) (hp : 1 ≤ p) : trY G x p hp ≫ prZ G x p = prZ G x 1 := by
  apply pullback.hom_ext
  · rw [Category.assoc, prZ_fst, prZ_fst, trY, pb, pb, ← Over.comp_left, whiskerRight_snd]
  · rw [Category.assoc, prZ_snd, prZ_snd, trY, ← Category.assoc, ← Over.comp_left, whiskerRight_fst, Over.comp_left,
      Category.assoc]
    congr 1
    exact spMap_comp_alg (S := k) _

end

end GlobalTheory.CompanionTheory.Ar.Coc

namespace GlobalTheory.CompanionTheory.Ar.Coc

theorem spMap_toΓ {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (a : A) :
    ((spMap f).appTop).hom (toΓ A a) = toΓ B (f a) :=
  (congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))).symm

section
variable {X0 : Scheme.{0}} (G : Over X0) {k : Type} [Field k] (x : Sp k ⟶ X0)

theorem dlt_pow (m : ℕ) : dlt G x m ^ (m + 1) = 0 := by
  rw [dlt, ← map_pow, ← map_pow, ← map_pow]
  have : (Ideal.Quotient.mk (orig k Unit ^ (m + 1))) (MvPolynomial.X () ) ^ (m + 1) = 0 := by
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.pow_mem_pow (X_mem_orig _) _)
  rw [map_pow, this, map_zero, map_zero]

theorem secZ_dlt (m : ℕ) : ((secZ G x m).appTop).hom (dlt G x m) = 0 := by
  have e := congrArg (fun q => (q.appTop).hom (toΓ (Jet k Unit m) (Ideal.Quotient.mk _ (MvPolynomial.X ())))) (secZ_fst G x m)
  simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at e
  rw [dlt, e, spMap_toΓ]
  have : ((jetAug : Jet k Unit m →ₐ[k] k) : Jet k Unit m →+* k) (Ideal.Quotient.mk _ (MvPolynomial.X ())) = 0 := by
    simp [jetAug, liftJet]
  rw [this, map_zero, map_zero]

theorem trY_dlt (p : ℕ) (hp : 1 ≤ p) : ((trY G x p hp).appTop).hom (dlt G x p) = dlt G x 1 := by
  have e : trY G x p hp ≫ (fst (Tm x p) G).left = (fst (Tm x 1) G).left ≫ (homAt x (toFirst k p hp)).left := by
    rw [trY, ← Over.comp_left, whiskerRight_fst, Over.comp_left]
  have e' := congrArg (fun q => (q.appTop).hom (toΓ (Jet k Unit p) (Ideal.Quotient.mk _ (MvPolynomial.X ())))) e
  simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at e'
  rw [dlt, e', dlt]
  congr 1
  exact spMap_toΓ _ _

theorem trY_pb (p : ℕ) (hp : 1 ≤ p) : trY G x p hp ≫ pb G x p = pb G x 1 := by
  rw [trY, pb, pb, ← Over.comp_left, whiskerRight_snd]

variable [GrpObj G]

theorem trY_pa (p : ℕ) (hp : 1 ≤ p) (y : Tm x p ⟶ G) :
    trY G x p hp ≫ pa G x y = pa G x (homAt x (toFirst k p hp) ≫ y) := by
  rw [trY, pa, pa, ← Over.comp_left, comp_lift_assoc, whiskerRight_snd, whiskerRight_fst_assoc]

theorem secZ_pa {m : ℕ} (y : Tm x m ⟶ G) (hy : homAt x (jetAug : Jet k Unit m →ₐ[k] k) ≫ y = 1) :
    secZ G x m ≫ pa G x y = pullback.fst G.hom x := by
  have hf : (Over.homMk (pullback.snd G.hom x ≫ spMap ((jetAug : Jet k Unit m →ₐ[k] k) : Jet k Unit m →+* k)) (by
      dsimp
      rw [Category.assoc, ← Category.assoc (spMap _), spMap_comp_alg]
      simp [spMap]) : FinalForm G x ⟶ Tm x m) ≫ y = 1 := by
    have e : (Over.homMk (pullback.snd G.hom x ≫ spMap ((jetAug : Jet k Unit m →ₐ[k] k) : Jet k Unit m →+* k)) (by
        dsimp
        rw [Category.assoc, ← Category.assoc (spMap _), spMap_comp_alg]
        simp [spMap]) : FinalForm G x ⟶ Tm x m) =
        (Over.homMk (pullback.snd G.hom x) (by simp [spMap]) : FinalForm G x ⟶ overAt x k) ≫ homAt x (jetAug : Jet k Unit m →ₐ[k] k) := by
      ext1
      rfl
    rw [e, Category.assoc, hy]
    simp [Hom.one_def]
  rw [secZ, pa, ← Over.comp_left, comp_lift_assoc, lift_fst_assoc, lift_snd, hf]
  exact congrArg (fun q => q.left) (_root_.one_mul (Over.homMk (pullback.fst G.hom x) pullback.condition : FinalForm G x ⟶ G))

end
end GlobalTheory.CompanionTheory.Ar.Coc

namespace GlobalTheory.CompanionTheory.Ar.Coc

theorem jet_pt {k : Type} [Field k] {κ : Type} (m : ℕ) (q : Sp (Jet k κ m)) (s : Sp k) :
    (spMap ((jetAug : Jet k κ m →ₐ[k] k) : Jet k κ m →+* k)) s = q := by
  have hs : Function.Surjective ((jetAug : Jet k κ m →ₐ[k] k) : Jet k κ m →+* k) := fun c =>
    ⟨algebraMap k _ c, (jetAug : Jet k κ m →ₐ[k] k).commutes c⟩
  have hm : (RingHom.ker ((jetAug : Jet k κ m →ₐ[k] k) : Jet k κ m →+* k)).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective _ hs
  have hq : (q : PrimeSpectrum (Jet k κ m)).asIdeal.IsPrime := (q : PrimeSpectrum (Jet k κ m)).isPrime
  have hle : RingHom.ker ((jetAug : Jet k κ m →ₐ[k] k) : Jet k κ m →+* k) ≤ (q : PrimeSpectrum (Jet k κ m)).asIdeal := by
    intro a ha
    obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective a
    have hc : MvPolynomial.constantCoeff P = 0 := by
      have : ((jetAug : Jet k κ m →ₐ[k] k) : Jet k κ m →+* k) (Ideal.Quotient.mk _ P) = MvPolynomial.constantCoeff P := by
        simp only [jetAug, liftJet]
        induction P using MvPolynomial.induction_on with
        | C c => simp
        | add a b ha hb => simp_all
        | mul_X a i ha => simp_all
      rw [← this]; exact ha
    have hP : P ∈ orig k κ := by simpa [hc] using sub_const_mem_orig P
    refine hq.mem_of_pow_mem (m + 1) ?_
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.pow_mem_pow hP _)]
    exact Ideal.zero_mem _
  have heq := hm.eq_of_le hq.ne_top hle
  have hb : ((s : PrimeSpectrum k).asIdeal) = ⊥ :=
    haveI : (s : PrimeSpectrum k).asIdeal.IsPrime := (s : PrimeSpectrum k).isPrime
    Ideal.eq_bot_of_prime _
  apply PrimeSpectrum.ext
  refine Eq.trans ?_ heq
  show Ideal.comap _ (s : PrimeSpectrum k).asIdeal = _
  rw [hb]
  rfl

section
variable {X0 : Scheme.{0}} (G : Over X0) [GrpObj G] {k : Type} [Field k] (x : Sp k ⟶ X0)

@[reassoc (attr := simp)]
theorem xkZ_fst {B : Type} [CommRing B] [Algebra k B] (z : overAt x B ⟶ G) :
    xkZ G x z ≫ pullback.fst G.hom x = z.left := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem xkZ_snd {B : Type} [CommRing B] [Algebra k B] (z : overAt x B ⟶ G) :
    xkZ G x z ≫ pullback.snd G.hom x = spMap (algebraMap k B) := pullback.lift_snd _ _ _

theorem rQ_pb {B : Type} [CommRing B] [Algebra k B] (p : ℕ) (z : overAt x B ⟶ G) :
    rQ G x p z ≫ pb G x p = spMap ((inR (k := k) B p : B →ₐ[k] Jet B Unit p) : B →+* Jet B Unit p) ≫ z.left := by
  rw [rQ, pb, ← Over.comp_left, lift_snd]; rfl

theorem rQ_fst {B : Type} [CommRing B] [Algebra k B] (p : ℕ) (z : overAt x B ⟶ G) :
    rQ G x p z ≫ (fst (Tm x p) G).left = spMap ((inL (k := k) B p : Jet k Unit p →ₐ[k] Jet B Unit p) : Jet k Unit p →+* Jet B Unit p) := by
  rw [rQ, ← Over.comp_left, lift_fst]; rfl

theorem rQ_prZ {B : Type} [CommRing B] [Algebra k B] (p : ℕ) (z : overAt x B ⟶ G) :
    rQ G x p z ≫ prZ G x p =
      spMap ((inR (k := k) B p : B →ₐ[k] Jet B Unit p) : B →+* Jet B Unit p) ≫ xkZ G x z := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, prZ_fst, xkZ_fst, rQ_pb]
  · rw [Category.assoc, Category.assoc, prZ_snd, xkZ_snd, ← Category.assoc, rQ_fst]
    exact (spMap_comp_alg (S := k) _).trans (spMap_comp_alg (S := k) _).symm

end

end GlobalTheory.CompanionTheory.Ar.Coc

namespace GlobalTheory.CompanionTheory.Ar.Coc

section
variable {k : Type} [Field k] {d : ℕ}

theorem dQ_span_pow (B : Type) [CommRing B] (p : ℕ) : Ideal.span {dQ B p} ^ (p + 1) = ⊥ := by
  rw [Ideal.span_singleton_pow, dQ_pow]
  simp

theorem mkX_span_pow (m : ℕ) :
    Ideal.span (Set.range fun q : Fin 1 × Fin d => (Ideal.Quotient.mk (orig k (Fin 1 × Fin d) ^ (m + 1)) (MvPolynomial.X q))) ^ (m + 1) = ⊥ := by
  have := map_orig_pow (R := k) (Ideal.Quotient.mk (orig k (Fin 1 × Fin d) ^ (m + 1))) (m + 1)
  rw [← this, Ideal.map_quotient_self]

def jq (w : Fin d → k) (p m : ℕ) :
    Jet k (Fin 2 × Fin d) (p + m + 1) →ₐ[k] Jet (Jet k (Fin 1 × Fin d) m) Unit p :=
  liftJet (MvPolynomial.aeval fun q : Fin 2 × Fin d =>
    if q.1 = 0 then algebraMap k _ (w q.2) * dQ (Jet k (Fin 1 × Fin d) m) p
    else inR (k := k) (Jet k (Fin 1 × Fin d) m) p (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), q.2)))) (by
    set B := Jet k (Fin 1 × Fin d) m
    set J₁ : Ideal (Jet B Unit p) := Ideal.span {dQ B p}
    set J₂ : Ideal (Jet B Unit p) := Ideal.map (inR (k := k) B p : B →+* Jet B Unit p)
      (Ideal.span (Set.range fun q : Fin 1 × Fin d => (Ideal.Quotient.mk (orig k (Fin 1 × Fin d) ^ (m + 1)) (MvPolynomial.X q))))
    have h₁ : J₁ ^ (p + 1) = ⊥ := dQ_span_pow B p
    have h₂ : J₂ ^ (m + 1) = ⊥ := by
      rw [← Ideal.map_pow, mkX_span_pow, Ideal.map_bot]
    have hle : Ideal.span (Set.range fun i : Fin 2 × Fin d => (MvPolynomial.aeval (R := k) fun q : Fin 2 × Fin d =>
        if q.1 = 0 then algebraMap k _ (w q.2) * dQ B p
        else inR (k := k) B p (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), q.2)))) (MvPolynomial.X i)) ≤ J₁ ⊔ J₂ := by
      rw [Ideal.span_le]
      rintro _ ⟨q, rfl⟩
      simp only [MvPolynomial.aeval_X]
      split_ifs
      · exact Ideal.mem_sup_left (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))
      · exact Ideal.mem_sup_right (Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨(0, q.2), rfl⟩))
    apply le_bot_iff.1
    refine (Ideal.pow_right_mono hle _).trans ?_
    have := Ideal.sup_pow_add_le_pow_sup_pow (I := J₁) (J := J₂) (n := p + 1) (m := m + 1)
    rw [h₁, h₂, bot_sup_eq] at this
    have e : p + m + 1 + 1 = p + 1 + (m + 1) := by omega
    rw [e]
    exact this)

end

end GlobalTheory.CompanionTheory.Ar.Coc

namespace GlobalTheory.CompanionTheory.Ar.Coc

theorem toΓ_inj (A : Type) [CommRing A] : Function.Injective (toΓ A) :=
  (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).inv).1

end GlobalTheory.CompanionTheory.Ar.Coc
