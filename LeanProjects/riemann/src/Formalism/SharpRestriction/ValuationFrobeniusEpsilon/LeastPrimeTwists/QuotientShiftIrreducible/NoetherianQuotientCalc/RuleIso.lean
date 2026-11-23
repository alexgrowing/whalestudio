import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.EulerVanishingBelowDimension

noncomputable section

namespace Formalism.MainNotions.V.Pf.V2.Calc

variable {k : ℕ} {B R : Type} [CommRing B] [CommRing R] [Algebra B R]

namespace GIso

variable {F G : GMod B R k}

theorem mem_gr_iff (φ : GIso F G) (m : Deg k) (x : F.M) : φ.e x ∈ G.gr m ↔ x ∈ F.gr m := by
  rw [← φ.map_gr m]
  constructor
  · rintro ⟨y, hy, hxy⟩
    have : y = x := φ.e.injective hxy
    exact this ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

def grEquiv (φ : GIso F G) (m : Deg k) : F.gr m ≃ₗ[B] G.gr m :=
  LinearEquiv.ofSubmodules (φ.e.restrictScalars B) (F.gr m) (G.gr m) (by
    rw [← φ.map_gr m]; rfl)

def sub (φ : GIso F G) (N : Submodule R F.M) (N' : Submodule R G.M)
    (h : N.map (φ.e : F.M →ₗ[R] G.M) = N') : GIso (F.sub N) (G.sub N') where
  e := LinearEquiv.ofSubmodules φ.e N N' h
  map_gr m := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (φ.mem_gr_iff m x.1).2 hx
    · intro hy
      refine ⟨(LinearEquiv.ofSubmodules φ.e N N' h).symm y, ?_, ?_⟩
      · have h1 : φ.e ((LinearEquiv.ofSubmodules φ.e N N' h).symm y).1 = y.1 := by
          have := congrArg Subtype.val
            ((LinearEquiv.ofSubmodules φ.e N N' h).apply_symm_apply y)
          exact this
        have h2 : φ.e ((LinearEquiv.ofSubmodules φ.e N N' h).symm y).1 ∈ G.gr m := by
          rw [h1]; exact hy
        exact (φ.mem_gr_iff m _).1 h2
      · exact (LinearEquiv.ofSubmodules φ.e N N' h).apply_symm_apply y

def quo (φ : GIso F G) (N : Submodule R F.M) (N' : Submodule R G.M)
    (h : N.map (φ.e : F.M →ₗ[R] G.M) = N') : GIso (F.quo N) (G.quo N') where
  e := Submodule.Quotient.equiv N N' φ.e h
  map_gr m := by
    ext y
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨φ.e x, (φ.mem_gr_iff m x).2 hx, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      refine ⟨N.mkQ (φ.e.symm z), ⟨φ.e.symm z, ?_, rfl⟩, ?_⟩
      · apply (φ.mem_gr_iff m _).1
        rw [LinearEquiv.apply_symm_apply]; exact hz
      · show N'.mkQ (φ.e (φ.e.symm z)) = N'.mkQ z
        rw [LinearEquiv.apply_symm_apply]

def shift (φ : GIso F G) (d : Deg k) : GIso (F.shift d) (G.shift d) where
  e := φ.e
  map_gr m := φ.map_gr (m - d)

def quot (φ : GIso F G) (s : R) : GIso (F.quot s) (G.quot s) :=
  φ.quo _ _ (by
    ext y
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨φ.e x, (φ.e.map_smul s x).symm⟩
    · rintro ⟨z, rfl⟩
      refine ⟨s • φ.e.symm z, ⟨φ.e.symm z, rfl⟩, ?_⟩
      show φ.e (s • φ.e.symm z) = s • z
      rw [map_smul, LinearEquiv.apply_symm_apply])

def ann (φ : GIso F G) (s : R) (d : Deg k) : GIso (F.ann s d) (G.ann s d) :=
  (φ.sub _ _ (by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : s • x = 0 := hx
      show s • φ.e x = 0
      rw [← map_smul, hx', map_zero]
    · intro hy
      have hy' : s • y = 0 := hy
      refine ⟨φ.e.symm y, ?_, φ.e.apply_symm_apply y⟩
      show s • φ.e.symm y = 0
      rw [← map_smul, hy', map_zero])).shift d

end GIso

theorem chi_congr (ts : List (Deg k × R)) : ∀ (F G : GMod B R k), GIso F G →
    ∀ m, chi ts F m = chi ts G m := by
  induction ts with
  | nil =>
    intro F G φ m
    simp only [chi]
    rw [(φ.grEquiv m).length_eq]
  | cons p ts ih =>
    obtain ⟨d, s⟩ := p
    intro F G φ m
    simp only [chi]
    rw [ih _ _ (φ.quot s) m, ih _ _ (φ.ann s d) m]

theorem ruleIso : RuleIso := fun _ _ ts F G φ m => chi_congr ts F G φ m

end Formalism.MainNotions.V.Pf.V2.Calc
