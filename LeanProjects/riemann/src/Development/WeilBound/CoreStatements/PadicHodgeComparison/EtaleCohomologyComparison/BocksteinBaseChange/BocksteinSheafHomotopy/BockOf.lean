import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.EtProps
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.BocksteinLemmas

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry CochainComplex CochainComplex.HomComplex

namespace CrystallineSemistableComparison

open GlobalTheory.EtC

def IsMulSh {Q q : ℕ} (h : q ∣ Q) (i : ℤ) (ι : (restr (ZMod.castHom h (ZMod q))).obj (tw q i) ⟶ tw Q i) : Prop :=
  ∀ (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)) (ξ : Prim q Γ(U, ⊤)), ξ.1 = ζ.1 ^ (Q / q) →
    Sec.map ι (show Sec ((restr (ZMod.castHom h (ZMod q))).obj (tw q i)) U from twGen i ξ) = (Q / q) • twGen i ζ

def IsRedSh {Q q : ℕ} (h : q ∣ Q) (i : ℤ) (π : tw Q i ⟶ (restr (ZMod.castHom h (ZMod q))).obj (tw q i)) : Prop :=
  ∀ (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)) (ξ : Prim q Γ(U, ⊤)), ξ.1 = ζ.1 ^ (Q / q) →
    Sec.map π (twGen i ζ) = (show Sec ((restr (ZMod.castHom h (ZMod q))).obj (tw q i)) U from twGen i ξ)

theorem dvdA (p a b : ℕ) : p ^ a ∣ p ^ (a + b) := pow_dvd_pow p (Nat.le_add_right a b)

theorem dvdB (p a b : ℕ) : p ^ b ∣ p ^ (a + b) := pow_dvd_pow p (Nat.le_add_left b a)

def InTwSeq : Prop := ∀ (p a b : ℕ) [Fact p.Prime] (i : ℤ),
  ∃ (π : tw (p ^ (a + b)) i ⟶ (restr (ZMod.castHom (dvdB p a b) (ZMod (p ^ b)))).obj (tw (p ^ b) i))
    (π' : tw (p ^ (a + b)) i ⟶ (restr (ZMod.castHom (dvdA p a b) (ZMod (p ^ a)))).obj (tw (p ^ a) i))
    (l : kernel π ⟶ (restr (ZMod.castHom (dvdA p a b) (ZMod (p ^ a)))).obj (tw (p ^ a) i)),
    IsRedSh (dvdB p a b) i π ∧ IsRedSh (dvdA p a b) i π' ∧ Epi π ∧ p ^ a • kernel.ι π = 0 ∧
      kernel.ι π ≫ π' = p ^ b • l

def InRedSh : Prop := ∀ (Q q : ℕ) [NeZero Q] [NeZero q] (h : q ∣ Q) (i : ℤ)
  (π : tw Q i ⟶ (restr (ZMod.castHom h (ZMod q))).obj (tw q i)), IsRedSh h i π →
  ∀ (E : Spc) (n : ℤ) (z : Ht Q E n i),
    restrH (ZMod.castHom h (ZMod q)) E (tw q i) n (red Q q E n i z) = HK.post _ ((chains _).obj E) π n z

theorem bock_of (hS : InTwSeq) (hR : InRedSh) : BocksteinInputFromFormal := by
  intro hF p a b _ X _ n i z hz
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have : NeZero (p ^ (a + b)) := ⟨pow_ne_zero _ hp⟩
  have : NeZero (p ^ a) := ⟨pow_ne_zero _ hp⟩
  have : NeZero (p ^ b) := ⟨pow_ne_zero _ hp⟩
  obtain ⟨π, π', l, hπ, hπ', hepi, htor, hcomp⟩ := hS p a b i
  have hex : (ShortComplex.mk (kernel.ι π) π (kernel.condition π)).ShortExact :=
    { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel π) }
  obtain ⟨c, hc⟩ := hF.a7 (ZMod (p ^ (a + b))) _ hex
  have e1 := hR _ _ (dvdB p a b) i π hπ (sch.obj X) n z
  rw [hz, map_zero] at e1
  obtain ⟨w', hw'⟩ := ((hc ((chains (ZMod (p ^ (a + b)))).obj (sch.obj X)) n).1 z).1 e1.symm
  subst hw'
  refine ⟨?_, ?_⟩
  · change p ^ a • HK.post _ _ (kernel.ι π) n w' = 0
    rw [← PostcompositionHomotopy.post_nsmul, htor, PostcompositionHomotopy.post_zero]
  · have hA := hF.a8 _ _ (ZMod.castHom (dvdA p a b) (ZMod (p ^ a))) (sch.obj X) (tw (p ^ a) i) n
    obtain ⟨v, hv⟩ := hA.2 (HK.post _ _ l n w')
    refine ⟨v, hA.1 ?_⟩
    rw [hR _ _ (dvdA p a b) i π' hπ' (sch.obj X) n, map_nsmul, hv]
    change HK.post _ _ π' n (HK.post _ _ (kernel.ι π) n w') = _
    rw [← PostcompositionHomotopy.post_comp, hcomp, PostcompositionHomotopy.post_nsmul]

end CrystallineSemistableComparison
