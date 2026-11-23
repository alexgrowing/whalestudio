import Development.EtaleCohomology.EtaleSheaves.EtaleDegreeZeroCohomologyEquivLocallyConstantFun

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.E.LCSplitPf
open LateralTheory.E.t_E1Cut

def Idem : Prop := ∀ (q : ℕ) [NeZero q] (R : Type) [CommRing R] (φ : LocallyConstant (PrimeSpectrum R) (ZMod q)),
  ∃ ε : ZMod q → R, CompleteOrthogonalIdempotents ε ∧ ∀ (p : PrimeSpectrum R) (c : ZMod q), φ p = c ↔ ε c ∉ p.asIdeal

def Torsor : Prop := ∀ (q : ℕ) [NeZero q] (S : Type) [CommRing S] (f g : S), Ideal.span {f, g} = ⊤ →
  ∀ (φ : LocallyConstant (PrimeSpectrum (Localization.Away (f * g))) (ZMod q)) (ε : ZMod q → Localization.Away (f * g)),
  CompleteOrthogonalIdempotents ε → (∀ (p : PrimeSpectrum (Localization.Away (f * g))) (c : ZMod q), φ p = c ↔ ε c ∉ p.asIdeal) →
  ∃ (C : Type) (_ : CommRing C) (_ : Algebra S C), Algebra.Etale S C ∧ Module.Finite S C ∧
    Function.Surjective (PrimeSpectrum.comap (algebraMap S C)) ∧
    (Nonempty (C →ₐ[S] S) → ∃ a b, φ = lcMap (rL f g) a - lcMap (rR f g) b)

theorem LCSplit_of_idem (hF : FinEtSection) (hI : Idem) (hT : Torsor) : LCSplit := by
  intro q _ S _ hS f g hfg φ
  obtain ⟨ε, hε, hφ⟩ := hI q _ φ
  obtain ⟨C, _, _, hEt, hFin, hSurj, hsec⟩ := hT q S f g hfg φ ε hε hφ
  exact hsec (hF S C hS hSurj)

theorem idem_of : Idem := by
  intro q _ R _ φ
  classical
  let E := fun c : ZMod q => PrimeSpectrum.isIdempotentElemEquivClopens (R := R) |>.symm
    ⟨{x | φ x = c}, φ.isLocallyConstant.isClopen_fiber c⟩
  have hB : ∀ c, PrimeSpectrum.basicOpen (E c).1 = ⟨{x | φ x = c}, (φ.isLocallyConstant.isClopen_fiber c).isOpen⟩ :=
    fun c => PrimeSpectrum.basicOpen_isIdempotentElemEquivClopens_symm _
  have hmem : ∀ (p : PrimeSpectrum R) c, φ p = c ↔ (E c).1 ∉ p.asIdeal := by
    intro p c
    have := congrArg (fun U : TopologicalSpace.Opens (PrimeSpectrum R) => p ∈ U) (hB c)
    simp only [PrimeSpectrum.mem_basicOpen] at this
    exact (this.to_iff.trans (by rfl)).symm
  refine ⟨fun c => (E c).1, ?_, hmem⟩
  have hid : ∀ c, IsIdempotentElem (E c).1 := fun c => (E c).2
  have horth : OrthogonalIdempotents (fun c => (E c).1) := by
    refine ⟨hid, ?_⟩
    intro c d hcd
    apply IsIdempotentElem.eq_zero_of_isNilpotent ((hid c).mul (hid d))
    rw [nilpotent_iff_mem_prime]
    intro J hJ
    by_contra h
    have hc : (E c).1 ∉ J := fun hc => h (J.mul_mem_right _ hc)
    have hd : (E d).1 ∉ J := fun hd => h (J.mul_mem_left _ hd)
    exact hcd (((hmem ⟨J, hJ⟩ c).2 hc).symm.trans ((hmem ⟨J, hJ⟩ d).2 hd))
  refine CompleteOrthogonalIdempotents.of_prod_one_sub horth ?_
  have hP : IsIdempotentElem (∏ c, (1 - (E c).1)) := by
    classical
    induction (Finset.univ : Finset (ZMod q)) using Finset.induction_on with
    | empty => simpa using IsIdempotentElem.one
    | insert a s ha ih => rw [Finset.prod_insert ha]; exact (hid a).one_sub.mul ih
  apply IsIdempotentElem.eq_zero_of_isNilpotent hP
  rw [nilpotent_iff_mem_prime]
  intro J hJ
  rw [Ideal.IsPrime.prod_mem_iff]
  refine ⟨φ ⟨J, hJ⟩, Finset.mem_univ _, ?_⟩
  have hn : (E (φ ⟨J, hJ⟩)).1 ∉ J := (hmem ⟨J, hJ⟩ _).1 rfl
  have h0 : (E (φ ⟨J, hJ⟩)).1 * (1 - (E (φ ⟨J, hJ⟩)).1) ∈ J := by
    rw [mul_sub, mul_one, (hid _).eq, sub_self]; exact J.zero_mem
  exact (hJ.mem_or_mem h0).resolve_left hn

theorem LCSplit_of (hF : FinEtSection) (hT : Torsor) : LCSplit := LCSplit_of_idem hF idem_of hT

section Conc
variable {q : ℕ} [NeZero q] {A : Type} [CommRing A] {ε : ZMod q → A}

def twist (hε : CompleteOrthogonalIdempotents ε) : (ZMod q → A) →+* (ZMod q → A) where
  toFun z k := ∑ c, ε c * z (k + c)
  map_one' := by funext k; simp [hε.complete]
  map_zero' := by funext k; simp
  map_add' x y := by funext k; simp [mul_add, Finset.sum_add_distrib]
  map_mul' x y := by
    funext k
    simp only [Pi.mul_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_eq_single c]
    · rw [show ε c * x (k + c) * (ε c * y (k + c)) = (ε c * ε c) * (x (k + c) * y (k + c)) by ring, (hε.idem c).eq]
    · intro d _ hdc
      rw [show ε c * x (k + c) * (ε d * y (k + d)) = (ε c * ε d) * (x (k + c) * y (k + d)) by ring, hε.ortho (Ne.symm hdc), zero_mul]
    · simp
end Conc

section Tor
variable {q : ℕ} [NeZero q] {S : Type} [CommRing S] (f g : S) {ε : ZMod q → Localization.Away (f * g)}

abbrev Amb (q : ℕ) := (ZMod q → Localization.Away f) × (ZMod q → Localization.Away g)

def h1 : Amb f g q →+* (ZMod q → Localization.Away (f * g)) :=
  Pi.ringHom fun k => (rL f g).comp ((Pi.evalRingHom _ k).comp (RingHom.fst _ _))

def h2 (hε : CompleteOrthogonalIdempotents ε) : Amb f g q →+* (ZMod q → Localization.Away (f * g)) :=
  (twist hε).comp (Pi.ringHom fun k => (rR f g).comp ((Pi.evalRingHom _ k).comp (RingHom.snd _ _)))

def Tor (hε : CompleteOrthogonalIdempotents ε) : Subring (Amb f g q) := RingHom.eqLocus (h1 f g) (h2 f g hε)

def torMap (hε : CompleteOrthogonalIdempotents ε) : S →+* Tor f g hε :=
  RingHom.codRestrict (RingHom.prod ((Pi.constRingHom (ZMod q) _).comp (algebraMap S _))
    ((Pi.constRingHom (ZMod q) _).comp (algebraMap S _))) (Tor f g hε) (by
    intro s
    show h1 f g _ = h2 f g hε _
    funext k
    change rL f g (algebraMap S _ s) = ∑ c, ε c * rR f g (algebraMap S _ s)
    unfold rL rR
    rw [IsLocalization.Away.awayToAwayRight_eq, IsLocalization.Away.awayToAwayLeft_eq, ← Finset.sum_mul, hε.complete, one_mul])
end Tor

def TorEt : Prop := ∀ (q : ℕ) [NeZero q] (S : Type) [CommRing S] (f g : S), Ideal.span {f, g} = ⊤ →
  ∀ (ε : ZMod q → Localization.Away (f * g)) (hε : CompleteOrthogonalIdempotents ε),
  letI := (torMap f g hε).toAlgebra
  Algebra.Etale S (Tor f g hε) ∧ Module.Finite S (Tor f g hε) ∧
    Function.Surjective (PrimeSpectrum.comap (algebraMap S (Tor f g hε)))

def TorSec : Prop := ∀ (q : ℕ) [NeZero q] (S : Type) [CommRing S] (f g : S), Ideal.span {f, g} = ⊤ →
  ∀ (φ : LocallyConstant (PrimeSpectrum (Localization.Away (f * g))) (ZMod q)) (ε : ZMod q → Localization.Away (f * g))
  (hε : CompleteOrthogonalIdempotents ε), (∀ (p : PrimeSpectrum (Localization.Away (f * g))) (c : ZMod q), φ p = c ↔ ε c ∉ p.asIdeal) →
  letI := (torMap f g hε).toAlgebra
  Nonempty (Tor f g hε →ₐ[S] S) → ∃ a b, φ = lcMap (rL f g) a - lcMap (rR f g) b

theorem torsor_of (hE : TorEt) (hS : TorSec) : Torsor := by
  intro q _ S _ f g hfg φ ε hε hφ
  letI := (torMap f g hε).toAlgebra
  obtain ⟨h1, h2, h3⟩ := hE q S f g hfg ε hε
  exact ⟨Tor f g hε, inferInstance, (torMap f g hε).toAlgebra, h1, h2, h3, hS q S f g hfg φ ε hε hφ⟩

theorem LCSplit_of_tor (hF : FinEtSection) (hE : TorEt) (hS : TorSec) : LCSplit := LCSplit_of hF (torsor_of hE hS)

end LateralTheory.E.LCSplitPf
