import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormLeOneOfMemOL

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.Prism
open scoped Formalism.Per

namespace GlobalTheory.BKReal

variable {l : ℕ} [hl : Fact l.Prime]

theorem semiBC_of_basis {A B M N J : Type} [CommRing A] [CommRing B] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module B N] {f : A →+* B} {u : M →ₛₗ[f] N} (b : Module.Basis J A M)
    (c : Module.Basis J B N) (h : ∀ i, u (b i) = c i) : SemiBC u := by
  intro Q _ _ v
  refine ⟨c.constr B fun i => v (b i), fun x => ?_, fun w hw => c.ext fun i => ?_⟩
  · exact LinearMap.congr_fun (b.ext (f₁ := (c.constr B fun i => v (b i)).comp u) (f₂ := v) fun i => by
      rw [LinearMap.comp_apply, h, Module.Basis.constr_basis]) x
  · rw [Module.Basis.constr_basis, ← h, hw]

def piMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (J : Type) : (J → A) →ₛₗ[f] (J → B) where
  toFun x i := f (x i)
  map_add' x y := funext fun i => map_add f (x i) (y i)
  map_smul' c x := funext fun i => map_mul f c (x i)

theorem piMap_single {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {J : Type} [DecidableEq J] (i : J) :
    piMap f J (Pi.single i 1) = Pi.single i 1 := by
  ext1 k
  change f (Pi.single (M := fun _ => A) i 1 k) = _
  simp [Pi.single_apply, apply_ite f]

theorem semiBC_piMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (J : Type) [Fintype J]
    [DecidableEq J] : SemiBC (piMap f J) :=
  semiBC_of_basis (Pi.basisFun A J) (Pi.basisFun B J) fun i => by
    rw [Pi.basisFun_apply, Pi.basisFun_apply, piMap_single]

def piFrob {A : Type} [CommRing A] (φ : A →+* A) (d : A) (J : Type) :
    (J → A) →ₛₗ[(algebraMap A (Localization.Away d)).comp φ] LocalizedModule (Submonoid.powers d) (J → A) where
  toFun x := LocalizedModule.mk (piMap φ J x) 1
  map_add' x y := by simp [LocalizedModule.mk_add_mk]
  map_smul' c x := by
    rw [RingHom.comp_apply, algebraMap_smul, LocalizedModule.smul'_mk, LinearMap.map_smulₛₗ]

theorem exists_of_isFrac {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] {d : A} {y m : M} {k : ℕ}
    (h : IsFrac d (LocalizedModule.mk y 1) m k) : ∃ r : ℕ, d ^ r • d ^ k • y = d ^ r • m := by
  obtain ⟨⟨_, r, rfl⟩, hr⟩ := LocalizedModule.mk_eq.1 h
  exact ⟨r, by simpa [Submonoid.smul_def] using hr⟩

def unitPow (l : ℕ) (R : Type) [CommRing R] (J : Type) [Fintype J] [DecidableEq J] : FCrys l R where
  M P := J → P.A
  fin _ := inferInstance
  proj _ := inferInstance
  tr f := piMap f.f J
  tr_bc f := semiBC_piMap f.f J
  tr_id _ _ := rfl
  tr_comp _ _ _ := rfl
  Φ P d := piFrob P.D.φ d J
  Φ_bc P d := semiBC_of_basis (Pi.basisFun _ J) ((Pi.basisFun P.A J).ofIsLocalizedModule
    (Localization.Away (d : P.A)) (Submonoid.powers (d : P.A)) (LocalizedModule.mkLinearMap _ _)) fun i => by
      rw [Module.Basis.ofIsLocalizedModule_apply, Pi.basisFun_apply]
      exact congrArg (LocalizedModule.mk · 1) (piMap_single _ i)
  Φ_nat := by
    intro P P' f d d' x m k n j h1 h2
    obtain ⟨r, hr⟩ := exists_of_isFrac h1
    obtain ⟨s, hs⟩ := exists_of_isFrac h2
    refine ⟨r + s, funext fun i => ?_⟩
    have ha : (d : P.A) ^ r * ((d : P.A) ^ k * P.D.φ (x i)) = (d : P.A) ^ r * m i := congrFun hr i
    have hb : (d' : P'.A) ^ s * ((d' : P'.A) ^ j * P'.D.φ (f.f (x i))) = (d' : P'.A) ^ s * n i := congrFun hs i
    have ha' := congrArg f.f ha
    simp only [map_mul, map_pow, f.f_φ] at ha'
    change (f.f d * d') ^ (r + s) * ((d' : P'.A) ^ j * f.f (m i) - f.f d ^ k * n i) = 0
    linear_combination (-(f.f d) ^ s * (d' : P'.A) ^ (r + s + j)) * ha' +
      (f.f d ^ (r + s + k) * (d' : P'.A) ^ r) * hb

def unitPowMap (F : FinExt l) {T J : Type} [AddCommGroup T] [Module ℤ_[l] T] [Fintype J] [DecidableEq J]
    (β : Module.Basis J ℤ_[l] T) : (unitPow l ↥(OL F) J).M (ainfObj F) →ₛₗ[(inclW l).comp (ainfId F).toRingHom]
      (WCb l ⊗[ℤ_[l]] T) :=
  (β.baseChange (WCb l)).equivFun.symm.toLinearMap.comp (piMap ((inclW l).comp (ainfId F).toRingHom) J)

theorem unitPowMap_apply (F : FinExt l) {T J : Type} [AddCommGroup T] [Module ℤ_[l] T] [Fintype J]
    [DecidableEq J] (β : Module.Basis J ℤ_[l] T) (x : J → Ainf l) :
    unitPowMap F β x = ∑ i, inclW l (x i) ⊗ₜ[ℤ_[l]] β i := by
  refine ((β.baseChange (WCb l)).equivFun_symm_apply fun i => inclW l (x i)).trans
    (Finset.sum_congr rfl fun i _ => ?_)
  rw [Module.Basis.baseChange_apply, smul_tmul', smul_eq_mul, mul_one]

theorem sum_frob {T J : Type} [AddCommGroup T] [Module ℤ_[l] T] [Fintype J] (β : J → T) {d : Ainf l}
    (hd : d ≠ 0) (x m : J → Ainf l) (k r : ℕ)
    (h : ∀ i, d ^ r * (d ^ k * WittVector.frobenius (x i)) = d ^ r * m i) :
    inclW l d ^ k • TensorProduct.map (frobW l).toLinearMap LinearMap.id (∑ i, inclW l (x i) ⊗ₜ[ℤ_[l]] β i) =
      ∑ i, inclW l (m i) ⊗ₜ[ℤ_[l]] β i := by
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [TensorProduct.map_tmul, AlgHom.toLinearMap_apply, LinearMap.id_apply, frobW_inclW,
    ← mul_left_cancel₀ (pow_ne_zero r hd) (h i), map_mul, map_pow, smul_tmul', smul_eq_mul]

theorem sum_gal {T J : Type} [AddCommGroup T] [Module ℤ_[l] T] [Fintype J] (β : J → T) (g : GQ l)
    (ρ : T →ₗ[ℤ_[l]] T) (hρ : ∀ x, ρ x = x) (x : J → Ainf l) :
    ∑ i, inclW l (Per.σA g (x i)) ⊗ₜ[ℤ_[l]] β i =
      TensorProduct.map (galW l g).toLinearMap ρ (∑ i, inclW l (x i) ⊗ₜ[ℤ_[l]] β i) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [TensorProduct.map_tmul, AlgEquiv.toLinearMap_apply, galW_inclW, hρ]

theorem unitPowMap_frob (F : FinExt l) {T J : Type} [AddCommGroup T] [Module ℤ_[l] T] [Fintype J]
    [DecidableEq J] (β : Module.Basis J ℤ_[l] T) (d : Ainf l) (hd : d ≠ 0) (x m : J → Ainf l) (k : ℕ)
    (h : IsFrac d (LocalizedModule.mk (piMap WittVector.frobenius J x) 1) m k) :
    inclW l d ^ k • TensorProduct.map (frobW l).toLinearMap LinearMap.id (unitPowMap F β x) =
      unitPowMap F β m := by
  obtain ⟨r, hr⟩ := exists_of_isFrac h
  rw [unitPowMap_apply, unitPowMap_apply]
  exact sum_frob β hd x m k r fun i => congrFun hr i

theorem unitPowMap_gal (F : FinExt l) {T J : Type} [AddCommGroup T] [Module ℤ_[l] T] [Fintype J]
    [DecidableEq J] (β : Module.Basis J ℤ_[l] T) (g : GQ l) (ρ : T →ₗ[ℤ_[l]] T) (hρ : ∀ x, ρ x = x)
    (x : J → Ainf l) : unitPowMap F β (fun i => Per.σA g (x i)) =
      TensorProduct.map (galW l g).toLinearMap ρ (unitPowMap F β x) := by
  rw [unitPowMap_apply, unitPowMap_apply]
  exact sum_gal β g ρ hρ x

theorem realises_unitPow (F : FinExt l) {T J : Type} [AddCommGroup T] [Module ℤ_[l] T] [Fintype J]
    [DecidableEq J] (β : Module.Basis J ℤ_[l] T) (ρ : ↥(GK F) → (T →ₗ[ℤ_[l]] T)) (hρ : ∀ g x, ρ g x = x) :
    Realises F (unitPow l ↥(OL F) J) (ainfObj F) (ainfId F) T ρ (unitPowMap F β) where
  ainf := isAinf_ainfObj F
  bc := SemiBC.comp_equiv (semiBC_piMap ((inclW l).comp (ainfId F).toRingHom) J) _
  j_φ d hd x m k h := unitPowMap_frob F β d.1 hd x m k h
  j_act g x := unitPowMap_gal F β g (ρ g) (hρ g) x

end GlobalTheory.BKReal
