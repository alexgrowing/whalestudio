import Mathlib
import GroundTheory.PAdicHodge.UntiltFrobeniusEquivSymmEpsilonNeOne
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.ObFacts
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.MapAcrFromBase

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory AlgebraicGeometry GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.B

open PAlg

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O]

variable (l) in

structure Eps where
  e : ℕ → (Ob l)ˣ
  succ : ∀ k, e (k + 1) ^ l = e k
  one : theta0 l (WittVector.teichmuller l (e 0 : Ob l)) = 1
  prim : theta0 l (WittVector.teichmuller l (e 1 : Ob l)) ≠ 1

namespace Eps

variable (ε : Eps l)

def qk (k : ℕ) : Acris l := algebraMap (Ainf l) (Acris l) (WittVector.teichmuller l (ε.e k : Ob l))

def μ : Acris l := ε.qk 0 - 1

theorem cris_qk (A : PAlg l) (n k : ℕ) : A.cris n (ε.qk k) = A.toAcr n (WittVector.teichmuller l (A.s (ε.e k))) := by
  rw [qk, cris_algebraMap, sW, WittVector.map_teichmuller]

theorem sharp_e (A : PAlg l) : A.sharp (A.s (ε.e 0)) = 1 := by
  have := A.oC_theta0 (WittVector.teichmuller l (ε.e 0 : Ob l))
  rw [ε.one, map_one, sW, WittVector.map_teichmuller] at this
  exact this.symm

theorem μ_mem (k : Bool) (A : PAlg l) (n : ℕ) : A.cris n ε.μ ∈ JJ k A n := by
  have h := uJ_th k A n (WittVector.teichmuller l (A.s (ε.e 0)))
  have h' : A.th (WittVector.teichmuller l (A.s (ε.e 0))) = 1 := ε.sharp_e A
  rw [h', map_one] at h
  rw [μ, map_sub, map_one, cris_qk]
  exact Ideal.Quotient.eq.1 h.symm

def qU (n : ℕ) : ((base l).Acr n)ˣ :=
  Units.map (((base l).toAcr n).toMonoidHom.comp (WittVector.teichmuller l)) (ε.e 0)

theorem qU_val (n : ℕ) : (ε.qU n : (base l).Acr n) = (base l).cris n (ε.qk 0) := (ε.cris_qk (base l) n 0).symm

theorem qU_mem (k : Bool) (n : ℕ) : (ε.qU n : (bs l k n).R) - 1 ∈ (bs l k n).I := by
  have := ε.μ_mem k (base l) n
  rwa [μ, map_sub, map_one, ← qU_val] at this

end Eps

theorem mapU_sharp {A A' : PAlg l} (f : A ⟶ A') (a : A.A) : mapU f (A.sharp a) = A'.sharp (Hom.f f a) :=
  congrArg A'.th (WittVector.map_teichmuller _ _ _)

def epsU (ε : Eps l) (P : PAlg l ⥤ Type) : UF P.Elements where
  U T := (Units.map T.1.sharp).ker
  map {T T'} φ :=
    { toFun := fun x => ⟨Units.map (Hom.f φ.1).toMonoidHom x.1, by
        have h : T.1.sharp (x.1 : T.1.A) = 1 := congrArg Units.val (MonoidHom.mem_ker.1 x.2)
        refine MonoidHom.mem_ker.2 (Units.ext ?_)
        change T'.1.sharp (Hom.f φ.1 (x.1 : T.1.A)) = 1
        rw [← mapU_sharp, h, map_one]⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun _ _ => Subtype.ext (map_mul _ _ _) }
  map_id _ _ := rfl
  map_comp _ _ _ := rfl
  q T := ⟨Units.map T.1.s.toMonoidHom (ε.e 0), MonoidHom.mem_ker.2 (Units.ext (ε.sharp_e T.1))⟩
  map_q φ := Subtype.ext (Units.ext (RingHom.congr_fun (Hom.comm φ.1) _))

def contMap {A A' : PAlg l} (φ : A ⟶ A') (Γ : Type) [TopologicalSpace Γ] : A.cont Γ ⟶ A'.cont Γ where
  f := { toFun := fun f => ⟨fun z => Hom.f φ (f.1 z), fun k => (f.2 k).comp
           (Ideal.quotientMap (I := Ideal.span {A.pi ^ k}) (Ideal.span {A'.pi ^ k}) (Hom.f φ) (by
             rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]
             exact (RingHom.congr_fun (Hom.comm φ) (pFlat l)).symm ▸ Ideal.mem_span_singleton_self _))⟩
         map_one' := Subtype.ext (funext fun _ => map_one _)
         map_mul' := fun _ _ => Subtype.ext (funext fun _ => map_mul _ _ _)
         map_zero' := Subtype.ext (funext fun _ => map_zero _)
         map_add' := fun _ _ => Subtype.ext (funext fun _ => map_add _ _ _) }
  comm := RingHom.ext fun x => Subtype.ext (funext fun _ => RingHom.congr_fun (Hom.comm φ) x)

def contShift (A : PAlg l) : A.cont ℤ_[l] ⟶ A.cont ℤ_[l] where
  f := { toFun := fun f => ⟨fun z => f.1 (z + 1), fun k => (f.2 k).comp_continuous (continuous_add_right 1)⟩
         map_one' := rfl
         map_mul' := fun _ _ => rfl
         map_zero' := rfl
         map_add' := fun _ _ => rfl }
  comm := rfl

variable {F : Fn O} (κ : O →+* OC l)

structure Tower {d : ℕ} (s : F.Small d) : Type 1 where
  A : PAlg l
  g : s.R →+* A.U
  hg : g.comp s.a = A.oC.comp κ
  c : Fin d → ℕ → (A.A)ˣ
  c_succ : ∀ k m, c k (m + 1) ^ l = c k m
  c_sharp : ∀ k, A.sharp (c k 0) = g (s.T k)
  univ : ∀ (B : Type) [CommRing B] (o : Ob l →+* B) (g' : s.R →+* B) (ρ : Fin d → ℕ → B), o (pFlat l) = 0 →
    (∀ x w, theta0 l w = κ x → g' (s.a x) = o (w.coeff 0)) → (∀ k, ρ k 0 = g' (s.T k)) → (∀ k m, ρ k (m + 1) ^ l = ρ k m) →
    ∃! f : A.A →+* B, f.comp A.s = o ∧ (∀ r a, A.sharp a - g r ∈ Ideal.span {(l : A.U)} → f a = g' r) ∧ ∀ k m, f (c k m) = ρ k m

variable {κ} in

def Tower.obj {d : ℕ} {s : F.Small d} (𝒯 : Tower κ s) : (F.pt κ).Elements :=
  ⟨𝒯.A, F.Pt.map (CommRingCat.ofHom 𝒯.g) s.y₀, 𝒯.hg ▸ F.ov_map (CommRingCat.ofHom 𝒯.g) s.ov⟩

def Fn.Sub.inc (V : F.Sub) : Fn.Map V.fn F where
  u := { app := fun B => TypeCat.ofHom fun y => y.1
         naturality := fun _ _ _ => rfl }
  ov h := h

abbrev subEl (V : F.Sub) : El (V.fn.pt κ) ⥤ El (F.pt κ) := elMap (V.inc.pt κ)

theorem subEl_gT (V : F.Sub) (k : Bool) (n : ℕ) :
    gT V.fn κ k n ⋙ subThick V (bs l k n) rfl (κb κ k n) = subEl κ V ⋙ gT F κ k n := rfl

variable (F) in

abbrev flt (ε : Eps l) (k : Bool) (n : ℕ) (ρ : ℕ → ℕ) (hρ : Slow ρ) : Flt (Oc F κ k n) :=
  pdFlt (Lc F κ k n) ((base l).cris n) ρ hρ ε.μ (ε.μ_mem k (base l) n)

variable (l) in

def Local : Prop := ∀ d j : ℕ, ∃ N : ℕ, ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (ε : Eps l) (k : Bool) (n : ℕ)
  (ρ : ℕ → ℕ) (hρ : Slow ρ), n ≠ 0 → (k = false ∨ ρ = 0) → F.Small d →
    RI ((Polynomial.X : Polynomial ℤ) ^ N) j (flt F κ ε k n ρ hρ).rees (gT F κ k n)

variable (l) in

def Main : Prop := ∀ d j : ℕ, ∃ N : ℕ, ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (ε : Eps l), F.Atlas d →
  ∀ n : ℕ, (∀ k, UpTo (ε.μ ^ N) (β F κ k n j)) ∧ ∀ y, ∃ x ∈ HcFil F κ false n N j, β F κ false n j x = ε.μ ^ N • y

end CrystallineSemistableComparison.B
