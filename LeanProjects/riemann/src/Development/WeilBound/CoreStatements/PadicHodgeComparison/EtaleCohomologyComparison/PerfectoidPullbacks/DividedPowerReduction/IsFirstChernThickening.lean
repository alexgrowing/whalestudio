import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.IsFirstChernClassOfLineBundle
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.JEqPdPow
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Precomp

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb

section Cup
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R}

def sqP (b : IdF A) : CH.Pairing (sq (IdF.top A) b) (sq (IdF.top A) b) (sq (IdF.top A) b) where
  μ T := LinearMap.mk₂ R (fun (x y : sqM (IdF.top A) b T) => (⟨x.1 * y.1, Ideal.mul_mem_left _ _ y.2⟩ : sqM (IdF.top A) b T))
    (fun _ _ _ => Subtype.ext (add_mul _ _ _)) (fun _ _ _ => Subtype.ext (smul_mul_assoc _ _ _))
    (fun _ _ _ => Subtype.ext (mul_add _ _ _)) (fun _ _ _ => Subtype.ext (mul_smul_comm _ _ _))
  nat φ x y := Subtype.ext (map_mul (Ideal.quotientMapₐ _ (A.map φ).hom fun _ hx => b.map_mem φ hx) _ _).symm

end Cup

section Some
variable {b : Base} {L : b.Fun} (Q : ObjectProperty (Thick L))

def toSome (r : ℤ) (c : b.R) (j : ℕ) : HM Q none c j →ₗ[b.R] HM Q (some r) c j :=
  (sqLe (a := IdF.top _) (a' := IdF.top _) (b := stdI Q none c) (b' := stdI Q (some r) c) (fun _ => le_rfl)
    fun _ => sup_le_sup_right bot_le _).pull j

theorem toSome_redM (r : ℤ) (c : b.R) (j : ℕ) (z : HO Q j) : toSome Q r c j (redM Q none c j z) = redM Q (some r) c j z := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rfl

end Some

section C1
variable {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}}
  {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I}

def IsFirstChernThickening (Q : ObjectProperty (Thick (nlFun γ p X q κ))) (D : E.LineData X) (N : ℕ) (z : HO Q 2) : Prop :=
  ∀ (C : Type 1) [Category.{0} C] (G : C ⥤ Q.FullSubcategory), (∀ T, ∃ V ∈ 𝒱D D, InU V (G.obj T).obj) →
    ∀ Λ : B.CLift (q := q) (b := nlBase R I γ p) (ht := rfl) (κ := κ) (G ⋙ Q.ι) D,
      ∃ hz : CH.d (G ⋙ CH.modF (sP Q).A) 2 (Λ.coc (RingHom.id R) N) = 0,
        (CH.cx (G ⋙ CH.modF (sP Q).A)).cls _ hz = (CH.Mor.restrict (CH.modF (sP Q).A) G).pull 2 z

end C1

section NM
variable {O : Type} [CommRing O] {A A' : Type} [CommRing A] [CommRing A'] [Algebra O A] [Algebra O A'] {I : Ideal A} {I' : Ideal A'}
  {γ : DividedPowers I} {γ' : DividedPowers I'} {X X' : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {q' : X' ⟶ Spec (CommRingCat.of O)}
  {σ : A →+* A'} (m : NMor γ q (κA O I) γ' q' (κA O I') σ) (l s : ℕ)

theorem nm_mem (T : Thick (nlFun γ' 0 X' q' (κA O I'))) (h : TS γ' q' l s {⊤} T) : TS γ q l s {⊤} ((m.mor 0).obj T) :=
  ⟨h.1, ⊤, rfl, fun _ _ => trivial⟩

def nmS : SMor (sP (TS γ q l s {⊤})) (sP (TS γ' q' l s {⊤})) σ := m.smor _ _ (nm_mem m l s)

theorem nm_std (r : Option ℤ) (n : ℕ) : (nmS m l s).Le (stdI _ r ((l : A) ^ n)) (stdI _ r ((l : A') ^ n)) := by
  intro T x hx
  have e : (T.obj.i.comp σ) ((l : A) ^ n) = T.obj.i ((l : A') ^ n) := by rw [map_pow, map_pow, map_natCast, map_natCast]
  cases r
  · change x ∈ (⊥ : Ideal T.obj.B) ⊔ Ideal.span {(T.obj.i.comp σ) ((l : A) ^ n)} at hx
    rw [e] at hx; exact hx
  · change x ∈ (T.obj.pdPow _ : Ideal T.obj.B) ⊔ Ideal.span {(T.obj.i.comp σ) ((l : A) ^ n)} at hx
    rw [e] at hx; exact hx

def nmHM (r : Option ℤ) (n j : ℕ) : HM (TS γ q l s {⊤}) r ((l : A) ^ n) j →ₛₗ[σ] HM (TS γ' q' l s {⊤}) r ((l : A') ^ n) j :=
  ((nmS m l s).sq (a := IdF.top _) (a' := IdF.top _) (fun _ _ _ => trivial) (nm_std m l s r n)).pull j

def nmHO (j : ℕ) : HO (TS γ q l s {⊤}) j →ₛₗ[σ] HO (TS γ' q' l s {⊤}) j := (nmS m l s).o.pull j

end NM

end CrystallineSemistableComparison.Pb
