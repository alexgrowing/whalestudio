import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.MapUSharp
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ValuationOfValuationModSquare
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

noncomputable section

namespace GlobalTheory.CompanionTheory.PerfLift

variable {l : ℕ} [Fact l.Prime] {R S : Type} [CommRing R] [CommRing S]

def powHom (hS : (l : S) = 0) (n : ℕ) : S →+* S where
  toFun x := x ^ l ^ n
  map_one' := one_pow _
  map_mul' x y := mul_pow x y _
  map_zero' := zero_pow (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)
  map_add' x y := by
    obtain ⟨r, hr⟩ := exists_add_pow_prime_pow_eq (Fact.out : l.Prime) x y n
    rw [hr, hS]; simp

theorem powHom_apply (hS : (l : S) = 0) (n : ℕ) (x : S) : powHom hS n x = x ^ l ^ n := rfl

def rootHom [PerfectRing R l] (hR : (l : R) = 0) (n : ℕ) : R ≃+* R :=
  RingEquiv.ofBijective (powHom hR n)
    (PerfectRing.bijective_frobenius : Function.Bijective fun x : R => x ^ l ^ n)

theorem rootHom_pow [PerfectRing R l] (hR : (l : R) = 0) (n : ℕ) (a : R) :
    ((rootHom hR n).symm a) ^ l ^ n = a :=
  (rootHom hR n).apply_symm_apply a

theorem rootHom_symm_pow [PerfectRing R l] (hR : (l : R) = 0) (n : ℕ) (b : R) :
    (rootHom hR n).symm (b ^ l ^ n) = b :=
  (rootHom hR n).symm_apply_apply b

def level [PerfectRing R l] (hR : (l : R) = 0) (hS : (l : S) = 0) (π : S)
    (g : R →+* S ⧸ Ideal.span {π}) (n : ℕ) : R →+* S ⧸ Ideal.span {π} ^ l ^ n :=
  (Ideal.quotientMap (Ideal.span {π} ^ l ^ n) (powHom hS n)
    (fun _ hx => Ideal.mem_comap.2 (Ideal.pow_mem_pow hx _))).comp
      (g.comp ((rootHom hR n).symm : R →+* R))

theorem level_spec [PerfectRing R l] (hR : (l : R) = 0) (hS : (l : S) = 0) (π : S)
    (g : R →+* S ⧸ Ideal.span {π}) (n : ℕ) (b : R) (x : S)
    (hx : Ideal.Quotient.mk _ x = g b) :
    level hR hS π g n (b ^ l ^ n) = Ideal.Quotient.mk _ (x ^ l ^ n) := by
  have h1 : ((rootHom hR n).symm : R →+* R) (b ^ l ^ n) = b := rootHom_symm_pow hR n b
  simp only [level, RingHom.comp_apply, h1, ← hx, Ideal.quotientMap_mk, powHom_apply]

theorem strictMono_pow : StrictMono fun n : ℕ => l ^ n :=
  strictMono_nat_of_lt_succ fun n => Nat.pow_lt_pow_right (Fact.out : l.Prime).one_lt (Nat.lt_succ_self n)

theorem level_compat [PerfectRing R l] (hR : (l : R) = 0) (hS : (l : S) = 0) (π : S)
    (g : R →+* S ⧸ Ideal.span {π}) (m : ℕ) :
    (Ideal.Quotient.factorPow (Ideal.span {π}) ((strictMono_pow (l := l)).monotone m.le_succ)).comp
      (level hR hS π g (m + 1)) = level hR hS π g m := by
  ext a
  obtain ⟨b, rfl⟩ : ∃ b : R, b ^ l ^ (m + 1) = a := ⟨_, rootHom_pow hR (m + 1) a⟩
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (g b)
  have hx' : Ideal.Quotient.mk (Ideal.span {π}) (x ^ l) = g (b ^ l) := by
    rw [map_pow, map_pow, hx]
  have e1 : b ^ l ^ (m + 1) = (b ^ l) ^ l ^ m := by rw [← pow_mul, pow_succ']
  have e2 : x ^ l ^ (m + 1) = (x ^ l) ^ l ^ m := by rw [← pow_mul, pow_succ']
  rw [RingHom.comp_apply, level_spec hR hS π g (m + 1) b x hx, e1, level_spec hR hS π g m _ _ hx', e2]
  rfl

theorem exists_lift [PerfectRing R l] (hR : (l : R) = 0) (hS : (l : S) = 0) (π : S)
    [IsAdicComplete (Ideal.span {π}) S] (g : R →+* S ⧸ Ideal.span {π}) :
    ∃ f : R →+* S, (Ideal.Quotient.mk _).comp f = g := by
  refine ⟨IsAdicComplete.StrictMono.liftRingHom (Ideal.span {π}) (strictMono_pow (l := l))
    (level hR hS π g) (fun {m} => level_compat hR hS π g m), ?_⟩
  ext a
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (g a)
  have h0 := IsAdicComplete.StrictMono.mk_liftRingHom (Ideal.span {π}) (strictMono_pow (l := l))
    (level hR hS π g) (fun {m} => level_compat hR hS π g m) (n := 0) a
  have h1 := level_spec hR hS π g 0 a x hx
  have ea : a ^ l ^ 0 = a := by simp
  have ex : x ^ l ^ 0 = x := by simp
  rw [ea, ex] at h1
  have h2 := Ideal.Quotient.eq.1 (h0.trans h1)
  have eI : Ideal.span {π} ^ l ^ 0 = Ideal.span {π} := by simp
  rw [eI] at h2
  rw [RingHom.comp_apply, ← hx]
  exact Ideal.Quotient.eq.2 h2

theorem lift_unique [PerfectRing R l] (hR : (l : R) = 0) (hS : (l : S) = 0) (π : S)
    [IsHausdorff (Ideal.span {π}) S] (f f' : R →+* S)
    (h : (Ideal.Quotient.mk (Ideal.span {π})).comp f = (Ideal.Quotient.mk _).comp f') : f = f' := by
  apply DFunLike.coe_injective
  apply IsHausdorff.StrictMono.funext' (Ideal.span {π}) (strictMono_pow (l := l))
  intro n a
  obtain ⟨b, rfl⟩ : ∃ b : R, b ^ l ^ n = a := ⟨_, rootHom_pow hR n a⟩
  have hb : f b - f' b ∈ Ideal.span {π} :=
    Ideal.Quotient.eq.1 (RingHom.congr_fun h b)
  refine Ideal.Quotient.eq.2 ?_
  have e : f (b ^ l ^ n) - f' (b ^ l ^ n) = (f b - f' b) ^ l ^ n := by
    have := map_sub (powHom hS n) (f b) (f' b)
    simpa only [powHom_apply, map_pow] using this.symm
  rw [e]
  exact Ideal.pow_mem_pow hb _

theorem existsUnique_hom {l : ℕ} [Fact l.Prime] (A A' : PAlg l)
    (g : A.A →+* A'.A ⧸ Ideal.span {A'.pi})
    (hg : g.comp A.s = (Ideal.Quotient.mk _).comp A'.s) :
    ∃! φ : A ⟶ A', (Ideal.Quotient.mk _).comp (PAlg.Hom.f φ) = g := by
  have : IsAdicComplete (Ideal.span {A'.pi}) A'.A := A'.compl
  have hOb : ((l : ℕ) : Ob l) = 0 := CharP.cast_eq_zero _ l
  obtain ⟨f, hf⟩ := exists_lift A.natCast_l A'.natCast_l A'.pi g
  have hcomm : f.comp A.s = A'.s := by
    refine lift_unique hOb A'.natCast_l A'.pi _ _ ?_
    rw [← RingHom.comp_assoc, hf, hg]
  refine ⟨⟨f, hcomm⟩, hf, fun φ hφ => ?_⟩
  apply PAlg.Hom.ext
  exact lift_unique A.natCast_l A'.natCast_l A'.pi _ _ (hφ.trans hf.symm)

end GlobalTheory.CompanionTheory.PerfLift
