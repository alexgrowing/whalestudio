import Formalism.ConjugateSelfDual.StatementRest
import Mathlib
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LiftInvariantsFinrankEq
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.ScaledValuations.ValuationApplyLtOneIff
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.ScaledValuations.ScaleEps

noncomputable section

open NumberField Matrix

namespace Formalism.BasicNotions

namespace TV

structure XV where
  R : Ranks
  host : Host R

instance : CoeOut D7 XV := ⟨fun D => ⟨D.R, D.host⟩⟩

abbrev QbarQ : Type := AlgebraicClosure ℚ

abbrev GQ : Type := Formalism.ConjugateSelfDual.G ℚ QbarQ

abbrev QbarL (l : ℕ) [Fact l.Prime] : Type := Formalism.ConjugateSelfDual.Qbar l

instance (R : Ranks) : NeZero (4 * R.n) := ⟨Nat.pos_iff_ne_zero.mp (by simp only [Ranks.n]; positivity)⟩

def condV (D : XV) : ℕ := D.host.QS * D.host.q * D.host.d

abbrev GalE (D : XV) : Type := D.host.E ≃ₐ[ℚ] D.host.E

abbrev Chi (D : XV) : Type := GalE D →* Multiplicative (ZMod (4 * D.R.n))

def muC (D : XV) : Multiplicative (ZMod (4 * D.R.n)) →* ℂˣ :=
  Circle.toUnits.comp (ZMod.toCircle (N := 4 * D.R.n)).toMonoidHom

def chiC {D : XV} (χ : Chi D) : GalE D →* ℂˣ := (muC D).comp χ

abbrev eps (l : ℕ) [Fact l.Prime] : GQ →* ℤ_[l]ˣ := Formalism.MainNotions.V.Lang.cycZ ℚ QbarQ l

instance (D : XV) : Finite (Chi D) :=
  Finite.of_injective (fun f : Chi D => (f : GalE D → Multiplicative (ZMod (4 * D.R.n))))
    DFunLike.coe_injective

noncomputable instance (D : XV) : Fintype (Chi D) := Fintype.ofFinite _

def Jad3 (R : Type) [CommRing R] : Matrix (Fin 3) (Fin 3) R := !![0, 0, 1; 0, 1, 0; 1, 0, 0]

def Jsp4 (R : Type) [CommRing R] : Matrix (Fin 4) (Fin 4) R :=
  !![0, 0, 0, 1; 0, 0, 1, 0; 0, -1, 0, 0; -1, 0, 0, 0]

def wt4 : Fin 4 → (Fin 2 → ℤ) := ![![1, 1], ![0, 1], ![1, 0], ![0, 0]]

def psiRaw {D : XV} (O : Type) [CommRing O] (ζ : O) (res : GQ →* GalE D) (l : ℕ) [Fact l.Prime]
    [Algebra ℤ_[l] O] (e : ℕ) (χ : Chi D) (g : GQ) : O :=
  algebraMap ℤ_[l] O (eps l g : ℤ_[l]) ^ e * ζ ^ (Multiplicative.toAdd (χ (res g))).val

abbrev epsL (l : ℕ) [Fact l.Prime] : GQ →* (QbarL l)ˣ := Formalism.ConjugateSelfDual.cyc ℚ QbarQ l

def toLu {l : ℕ} [Fact l.Prime] (ι : QbarL l ≃+* ℂ) : ℂˣ →* (QbarL l)ˣ :=
  Units.map ι.symm.toRingHom.toMonoidHom

def chiLraw {D : XV} {l : ℕ} [Fact l.Prime] (ι : QbarL l ≃+* ℂ) (res : GQ →* GalE D) (χ : Chi D) :
    GQ →* (QbarL l)ˣ := (toLu ι).comp ((chiC χ).comp res)

def psiLraw {D : XV} {l : ℕ} [Fact l.Prime] (ι : QbarL l ≃+* ℂ) (res : GQ →* GalE D) (e : ℕ)
    (χ : Chi D) : GQ →* (QbarL l)ˣ := epsL l ^ e * chiLraw ι res χ

def toLZ {l : ℕ} [Fact l.Prime] (w : GQ →* ℤ_[l]ˣ) : GQ →* (QbarL l)ˣ :=
  (Units.map ((algebraMap ℚ_[l] (QbarL l)).comp PadicInt.Coe.ringHom).toMonoidHom).comp w

def xiLraw {l : ℕ} [Fact l.Prime] (ι : QbarL l ≃+* ℂ) (n' : ℕ) (ξ' : DirichletCharacter ℂ (2 ^ n')) :
    GQ →* (QbarL l)ˣ :=
  (toLu ι).comp ((MulChar.toUnitHom ξ').comp (Formalism.MainNotions.V.Lang.cycMod ℚ QbarQ 2 n'))

def alLraw {l : ℕ} [Fact l.Prime] (ι : QbarL l ≃+* ℂ) (w : GQ →* ℤ_[l]ˣ) (n' : ℕ)
    (ξ' : DirichletCharacter ℂ (2 ^ n')) : GQ →* (QbarL l)ˣ :=
  epsL l * (toLZ w)⁻¹ * xiLraw ι n' ξ'

def thLraw {D : XV} {l : ℕ} [Fact l.Prime] (ι : QbarL l ≃+* ℂ) (res : GQ →* GalE D)
    (w : GQ →* ℤ_[l]ˣ) (e : ℕ) (χ : Chi D) (n' : ℕ) (ξ' : DirichletCharacter ℂ (2 ^ n')) :
    GQ →* (QbarL l)ˣ :=
  alLraw ι w n' ξ' * psiLraw ι res e χ

def Qcyc (l : ℕ) [Fact l.Prime] (m : ℕ) : IntermediateField ℚ QbarQ :=
  IntermediateField.fixedField
    ((powMonoidHom (l - 1)).comp (Formalism.MainNotions.V.Lang.cycMod ℚ QbarQ l (m + 1))).ker

section VKdefs

open Formalism.ConjugateSelfDual Filter

def coef {N : ℕ} {k : ℤ} (f : CuspForm (CongruenceSubgroup.Gamma1 N) k) (n : ℕ) : ℂ :=
  (UpperHalfPlane.qExpansion 1 f).coeff n

def IsNewform {N : ℕ} {k : ℤ} (f : CuspForm (CongruenceSubgroup.Gamma1 N) k)
    (χ : DirichletCharacter ℂ N) : Prop :=
  0 < N ∧ IsNormEigenform f χ ∧
  ¬ ∃ M : ℕ, 0 < M ∧ M ∣ N ∧ M < N ∧ ∃ (χ' : DirichletCharacter ℂ M)
      (f' : CuspForm (CongruenceSubgroup.Gamma1 M) k), IsNormEigenform f' χ' ∧
      ∀ᶠ p in cofinite, p.Prime → coef f' p = coef f p

def CondDvd {H : Type*} [Monoid H] (χ : GQ →* H) (M : ℕ) : Prop :=
  ∀ σ : GQ, (∀ ζ : QbarQ, ζ ^ M = 1 → σ ζ = ζ) → χ σ = 1

def ActsBy (σ : GQ) (M a : ℕ) : Prop := ∀ ζ : QbarQ, ζ ^ M = 1 → σ ζ = ζ ^ a

open Classical in

def dirVal {l : ℕ} [Fact l.Prime] (φ : GQ →* (QbarL l)ˣ) (M a : ℕ) : QbarL l :=
  if h : ∃ σ, ActsBy σ M a then ((φ h.choose : (QbarL l)ˣ) : QbarL l) else 0

def twC (l : ℕ) [Fact l.Prime] (j : ℤ) (φ : GQ →* (QbarL l)ˣ) : GQ →* (QbarL l)ˣ := epsL l ^ j * φ

def IsVgTw (l : ℕ) [Fact l.Prime] {N : ℕ} {k : ℤ} (f : CuspForm (CongruenceSubgroup.Gamma1 N) k)
    (j : ℤ) (ι : QbarL l →+* ℂ) (φ : GQ →* (QbarL l)ˣ) (W : GQ →* GL (Fin 2) (QbarL l)) : Prop :=
  Continuous W ∧ ∀ᶠ v in cofinite, ∀ (A : ValuationSubring QbarQ) (σ : GQ),
    IsPlaceOver (F := ℚ) A v → IsFrob A (normV v) σ →
      ι (W σ : Matrix (Fin 2) (Fin 2) (QbarL l)).trace =
        starRingEnd ℂ (coef f (normV v)) * ((normV v : ℕ) : ℂ) ^ (j - (k - 1)) * ι (φ σ : QbarL l)

def twGL {l : ℕ} [Fact l.Prime] (W : GQ →* GL (Fin 2) (QbarL l)) (χ : GQ →* (QbarL l)ˣ) :
    GQ →* GL (Fin 2) (QbarL l) where
  toFun σ := Units.map (algebraMap (QbarL l) (Matrix (Fin 2) (Fin 2) (QbarL l))).toMonoidHom (χ σ) * W σ
  map_one' := by simp
  map_mul' σ τ := by
    ext1
    simp only [map_mul, Units.val_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe,
      MonoidHom.coe_coe]
    rw [mul_assoc, mul_assoc, ← mul_assoc (W σ : Matrix (Fin 2) (Fin 2) (QbarL l)),
      ← Algebra.commutes, mul_assoc]

def glMap {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [Algebra ℚ_[l] E] (emb : E →ₐ[ℚ_[l]] QbarL l)
    (W : GQ →* GL (Fin 2) E) : GQ →* GL (Fin 2) (QbarL l) :=
  (Units.map (emb.toRingHom.mapMatrix : Matrix (Fin 2) (Fin 2) E →+* Matrix (Fin 2) (Fin 2) (QbarL l)).toMonoidHom).comp W

def conjGL {l n : ℕ} [Fact l.Prime] (M : GL (Fin n) (QbarL l)) (ρ : GQ →* GL (Fin n) (QbarL l)) :
    GQ →* GL (Fin n) (QbarL l) := (MulAut.conj M).toMonoidHom.comp ρ

def Z1 {l n : ℕ} [Fact l.Prime] (ρ : GQ →* GL (Fin n) (QbarL l)) :
    Submodule (QbarL l) (GQ → (Fin n → QbarL l)) where
  carrier := {c | Continuous c ∧ ∀ σ τ, c (σ * τ) = c σ + (ρ σ : Matrix (Fin n) (Fin n) (QbarL l)).mulVec (c τ)}
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨ha.add hb, fun σ τ => ?_⟩
    simp only [Pi.add_apply, ha' σ τ, hb' σ τ, Matrix.mulVec_add]
    abel
  zero_mem' := ⟨continuous_const, fun σ τ => by simp⟩
  smul_mem' := by
    rintro a c ⟨hc, hc'⟩
    refine ⟨hc.const_smul a, fun σ τ => ?_⟩
    simp only [Pi.smul_apply, hc' σ τ, smul_add, Matrix.mulVec_smul]

def cobd {l n : ℕ} [Fact l.Prime] (ρ : GQ →* GL (Fin n) (QbarL l)) :
    (Fin n → QbarL l) →ₗ[QbarL l] (GQ → (Fin n → QbarL l)) :=
  LinearMap.pi fun σ => Matrix.mulVecLin (ρ σ : Matrix (Fin n) (Fin n) (QbarL l)) - LinearMap.id

def B1 {l n : ℕ} [Fact l.Prime] (ρ : GQ →* GL (Fin n) (QbarL l)) :
    Submodule (QbarL l) (GQ → (Fin n → QbarL l)) := LinearMap.range (cobd ρ)

def CobOn {l n : ℕ} [Fact l.Prime] (ρ : GQ →* GL (Fin n) (QbarL l)) (c : GQ → (Fin n → QbarL l))
    (H : Subgroup GQ) : Prop :=
  ∃ m : Fin n → QbarL l, ∀ σ ∈ H, c σ = (ρ σ : Matrix (Fin n) (Fin n) (QbarL l)).mulVec m - m

def unrP (P : ℕ → ValuationSubring QbarQ) (l : ℕ) [Fact l.Prime] {n : ℕ} (ρ : GQ →* GL (Fin n) (QbarL l)) :
    Submodule (QbarL l) (GQ → (Fin n → QbarL l)) where
  carrier := {c | ∀ q : ℕ, q.Prime → q ≠ l → CobOn ρ c (Formalism.MainNotions.V.Lang.Ine (F := ℚ) (P q))}
  add_mem' := by
    intro a b ha hb q hq hql
    obtain ⟨m, hm⟩ := ha q hq hql
    obtain ⟨m', hm'⟩ := hb q hq hql
    refine ⟨m + m', fun σ hσ => ?_⟩
    simp only [Pi.add_apply, hm σ hσ, hm' σ hσ, Matrix.mulVec_add]
    abel
  zero_mem' := fun q _ _ => ⟨0, fun σ _ => by simp⟩
  smul_mem' := by
    intro a c hc q hq hql
    obtain ⟨m, hm⟩ := hc q hq hql
    refine ⟨a • m, fun σ hσ => ?_⟩
    simp only [Pi.smul_apply, hm σ hσ, Matrix.mulVec_smul, smul_sub]

def SelP (P : ℕ → ValuationSubring QbarQ) (l : ℕ) [Fact l.Prime] {n : ℕ} (ρ : GQ →* GL (Fin n) (QbarL l))
    (L : Submodule (QbarL l) (GQ → (Fin n → QbarL l))) : Submodule (QbarL l) (GQ → (Fin n → QbarL l)) :=
  Z1 ρ ⊓ unrP P l ρ ⊓ L

open Classical in

def LCont (b : ℕ → ℂ) (c : ℝ) (s : ℂ) : ℂ :=
  if h : ∃ F : ℂ → ℂ, Differentiable ℂ F ∧ ∀ z : ℂ, c < z.re → F z = LSeries b z then h.choose s else 0

structure KatoSys (P : ℕ → ValuationSubring QbarQ) (l : ℕ) [Fact l.Prime] (e : ℕ) {N : ℕ}
    (f : CuspForm (CongruenceSubgroup.Gamma1 N) ((2 * e + 1 : ℕ) : ℤ)) (ι : QbarL l →+* ℂ)
    (DdR : ∀ n : ℕ, (GQ →* GL (Fin n) (QbarL l)) → Type) [∀ n ρ, AddCommGroup (DdR n ρ)]
    [∀ n ρ, Module (QbarL l) (DdR n ρ)]
    (expS : ∀ n ρ, (GQ → (Fin n → QbarL l)) →ₗ[QbarL l] DdR n ρ) where

  E : Type
  [instE : Field E]
  [instEalg : Algebra ℚ_[l] E]
  [instEfd : FiniteDimensional ℚ_[l] E]
  emb : E →ₐ[ℚ_[l]] QbarL l

  VgE : GQ →* GL (Fin 2) E
  Vg_tr : IsVgTw l f 0 ι 1 (glMap emb VgE)

  abelian₂ : Type
  [instLam : CommRing abelian₂]
  [instLamAlg : Algebra E abelian₂]

  HH1 : Type
  [instAddCommGroupH1Alt : AddCommGroup HH1]
  [instModuleH1Alt : Module abelian₂ HH1]
  HH2 : Type
  [instAddCommGroupH2Alt : AddCommGroup HH2]
  [instModuleH2Alt : Module abelian₂ HH2]

  z : (Fin 2 → E) → HH1

  spChar : ℕ → (GQ →* (QbarL l)ˣ) → (abelian₂ →+* QbarL l)
  spChar_E : ∀ (r : ℕ) φ' (a : E), spChar r φ' (algebraMap E abelian₂ a) = emb a

  spec : ℕ → (GQ →* (QbarL l)ˣ) → HH1 → (GQ → (Fin 2 → QbarL l))
  euler_system_cocycle : ∀ (r : ℕ) φ' x, spec r φ' x ∈ Z1 (twGL (glMap emb VgE) (twC l (((2 * e + 1 : ℕ) : ℤ) - (r : ℤ)) φ'))
  spec_unr : ∀ (r : ℕ) φ' x, spec r φ' x ∈ unrP P l (twGL (glMap emb VgE) (twC l (((2 * e + 1 : ℕ) : ℤ) - (r : ℤ)) φ'))
  spec_add : ∀ (r : ℕ) φ' x y, spec r φ' (x + y) - spec r φ' x - spec r φ' y ∈
    B1 (twGL (glMap emb VgE) (twC l (((2 * e + 1 : ℕ) : ℤ) - (r : ℤ)) φ'))
  spec_smul : ∀ (r : ℕ) φ' (a : abelian₂) x, spec r φ' (a • x) - spChar r φ' a • spec r φ' x ∈
    B1 (twGL (glMap emb VgE) (twC l (((2 * e + 1 : ℕ) : ℤ) - (r : ℤ)) φ'))

  per : ∀ (r : ℕ) φ', DdR 2 (twGL (glMap emb VgE) (twC l (((2 * e + 1 : ℕ) : ℤ) - (r : ℤ)) φ')) →+ (Fin 2 → ℂ)

attribute [instance] KatoSys.instE KatoSys.instEalg KatoSys.instEfd KatoSys.instLam KatoSys.instLamAlg
  KatoSys.instAddCommGroupH1Alt KatoSys.instModuleH1Alt KatoSys.instAddCommGroupH2Alt KatoSys.instModuleH2Alt

def KatoSys.tw {P : ℕ → ValuationSubring QbarQ} {l : ℕ} [Fact l.Prime] {e N : ℕ}
    {f : CuspForm (CongruenceSubgroup.Gamma1 N) ((2 * e + 1 : ℕ) : ℤ)} {ι : QbarL l →+* ℂ}
    {DdR : ∀ n : ℕ, (GQ →* GL (Fin n) (QbarL l)) → Type} [∀ n ρ, AddCommGroup (DdR n ρ)]
    [∀ n ρ, Module (QbarL l) (DdR n ρ)] {expS : ∀ n ρ, (GQ → (Fin n → QbarL l)) →ₗ[QbarL l] DdR n ρ}
    (S : KatoSys P l e f ι DdR expS) (r : ℕ) (φ' : GQ →* (QbarL l)ˣ) : GQ →* GL (Fin 2) (QbarL l) :=
  twGL (glMap S.emb S.VgE) (twC l (((2 * e + 1 : ℕ) : ℤ) - (r : ℤ)) φ')

def KatoSys.pm {P : ℕ → ValuationSubring QbarQ} {l : ℕ} [Fact l.Prime] {e N : ℕ}
    {f : CuspForm (CongruenceSubgroup.Gamma1 N) ((2 * e + 1 : ℕ) : ℤ)} {ι : QbarL l →+* ℂ}
    {DdR : ∀ n : ℕ, (GQ →* GL (Fin n) (QbarL l)) → Type} [∀ n ρ, AddCommGroup (DdR n ρ)]
    [∀ n ρ, Module (QbarL l) (DdR n ρ)] {expS : ∀ n ρ, (GQ → (Fin n → QbarL l)) →ₗ[QbarL l] DdR n ρ}
    (S : KatoSys P l e f ι DdR expS) (c : GQ) (s : S.E) (v : Fin 2 → S.E) : Fin 2 → S.E :=
  (2⁻¹ : S.E) • (v + s • (S.VgE c : Matrix (Fin 2) (Fin 2) S.E).mulVec v)

end VKdefs

section ShaDefs

variable (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M]

def twistedCocycles (H : Subgroup GQ) (w : GQ → R) : Submodule R (H → M) where
  carrier := {c | IsLocallyConstant c ∧ ∀ g h : H, c (g * h) = c g + w g • c h}
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨ha.add hb, fun g h => ?_⟩
    simp only [Pi.add_apply, ha' g h, hb' g h, smul_add]
    abel
  zero_mem' := ⟨IsLocallyConstant.const 0, fun g h => by simp⟩
  smul_mem' := by
    rintro r c ⟨hc, hc'⟩
    refine ⟨hc.comp (fun m => r • m), fun g h => ?_⟩
    simp only [Pi.smul_apply, hc' g h, smul_add, smul_comm r (w g)]

def cobdw (H : Subgroup GQ) (w : GQ → R) : M →ₗ[R] (H → M) where
  toFun m g := w g • m - m
  map_add' m m' := by
    funext g
    simp only [Pi.add_apply, smul_add]
    abel
  map_smul' r m := by
    funext g
    simp only [Pi.smul_apply, RingHom.id_apply, smul_sub, smul_comm r (w g)]

def twistedCoboundaries (H : Subgroup GQ) (w : GQ → R) : Submodule R (H → M) := LinearMap.range (cobdw R M H w)

def CobOnw {H : Subgroup GQ} {w : GQ → R} (c : H → M) (H' : Subgroup GQ) : Prop :=
  ∃ m : M, ∀ g : H, (g : GQ) ∈ H' → c g = w g • m - m

def locw (H : Subgroup GQ) (w : GQ → R) (Cs : Set (Subgroup GQ)) : Submodule R (H → M) where
  carrier := {c | ∀ H' ∈ Cs, CobOnw R M (w := w) c H'}
  add_mem' := by
    intro a b ha hb H' hH'
    obtain ⟨m, hm⟩ := ha H' hH'
    obtain ⟨m', hm'⟩ := hb H' hH'
    refine ⟨m + m', fun g hg => ?_⟩
    simp only [Pi.add_apply, hm g hg, hm' g hg, smul_add]
    abel
  zero_mem' := fun H' _ => ⟨0, fun g _ => by simp⟩
  smul_mem' := by
    intro r c hc H' hH'
    obtain ⟨m, hm⟩ := hc H' hH'
    refine ⟨r • m, fun g hg => ?_⟩
    simp only [Pi.smul_apply, hm g hg, smul_sub, smul_comm r (w g)]

abbrev Z1loc (H : Subgroup GQ) (w : GQ → R) (Cs : Set (Subgroup GQ)) : Submodule R (H → M) :=
  twistedCocycles R M H w ⊓ locw R M H w Cs

abbrev SelmerGroupAlt (H : Subgroup GQ) (w : GQ → R) (Cs : Set (Subgroup GQ)) : Type :=
  Z1loc R M H w Cs ⧸ (twistedCoboundaries R M H w).comap (Z1loc R M H w Cs).subtype

end ShaDefs

abbrev QZ (l : ℕ) [Fact l.Prime] : Type := ℚ_[l] ⧸ (1 : Submodule ℤ_[l] ℚ_[l])

abbrev KO (O : Type) [CommRing O] [IsDomain O] : Type := FractionRing O ⧸ (1 : Submodule O (FractionRing O))

abbrev GEof {E : Type} [Field E] [Algebra ℚ E] (embE : E →ₐ[ℚ] QbarQ) : Subgroup GQ :=
  embE.fieldRange.fixingSubgroup

def epsNeg (l : ℕ) [Fact l.Prime] (e : ℕ) (g : GQ) : ℤ_[l] := (((eps l g)⁻¹ ^ e : ℤ_[l]ˣ) : ℤ_[l])

def shaCondsE (l : ℕ) : Set (Subgroup GQ) :=
  {H' | ∃ A : ValuationSubring QbarQ,
    (Formalism.MainNotions.V.Lang.IsFinitePlace ℚ A ∧ ¬ Formalism.MainNotions.V.Lang.IsPlaceAbove ℚ A l ∧
              H' = Formalism.MainNotions.V.Lang.Ine (F := ℚ) A) ∨
      (Formalism.MainNotions.V.Lang.IsPlaceAbove ℚ A l ∧ H' = Formalism.MainNotions.V.Lang.Dec (F := ℚ) A)}

abbrev ShaE {E : Type} [Field E] [Algebra ℚ E] (embE : E →ₐ[ℚ] QbarQ) (l : ℕ) [Fact l.Prime] (e : ℕ) :
    Type :=
  SelmerGroupAlt ℤ_[l] (QZ l) (GEof embE) (epsNeg l e) (shaCondsE l)

section univ

open IsLocalRing

def InCO (O : Type) [CommRing O] [IsLocalRing O] (A : Type) [CommRing A] [IsLocalRing A]
    [Algebra O A] : Prop :=
  IsNoetherianRing A ∧ IsAdicComplete (maximalIdeal A) A ∧ IsLocalHom (algebraMap O A) ∧
    Function.Surjective (fun x : O => residue A (algebraMap O A x))

def diag4 {O : Type} [CommRing O] (c : Fin 4 → GQ → O) (g : GQ) : Matrix (Fin 4) (Fin 4) O :=
  Matrix.diagonal fun i => c i g

def diagN {O : Type} [CommRing O] {n : ℕ} (c : Fin n → GQ → O) (g : GQ) : Matrix (Fin n) (Fin n) O :=
  Matrix.diagonal fun i => c i g

def IsLiftOn (O : Type) [CommRing O] [IsLocalRing O] (H : Subgroup GQ) (ν : GQ → O)
    (c : Fin 4 → GQ → O) (A : Type) [CommRing A] [IsLocalRing A] [Algebra O A]
    (s : H →* GL (Fin 4) A) : Prop :=
  (∀ n : ℕ, ∃ U : Subgroup GQ, IsOpen (U : Set GQ) ∧
    ∀ h : H, h.1 ∈ U → ∀ i j, ((s h : Matrix (Fin 4) (Fin 4) A) - 1) i j ∈ maximalIdeal A ^ n) ∧
  (∀ h : H, (s h : Matrix (Fin 4) (Fin 4) A)ᵀ * Jsp4 A * (s h : Matrix (Fin 4) (Fin 4) A) =
    algebraMap O A (ν h) • Jsp4 A) ∧
  (∀ h : H, (s h : Matrix (Fin 4) (Fin 4) A).map (residue A) =
    (diag4 c h).map (fun x => residue A (algebraMap O A x)))

def IsUnivLift (O : Type) [CommRing O] [IsLocalRing O] (H : Subgroup GQ) (ν : GQ → O)
    (c : Fin 4 → GQ → O) (P : ∀ (A : Type) [CommRing A] [IsLocalRing A] [Algebra O A],
      (H →* GL (Fin 4) A) → Prop)
    (R : Type) [CommRing R] [IsLocalRing R] [Algebra O R] (s : H →* GL (Fin 4) R) : Prop :=
  InCO O R ∧ IsLiftOn O H ν c R s ∧ P R s ∧
  ∀ (A : Type) [CommRing A] [IsLocalRing A] [Algebra O A], InCO O A →
    ∀ s' : H →* GL (Fin 4) A, IsLiftOn O H ν c A s' → P A s' →
      ∃! φ : R →ₐ[O] A, IsLocalHom (φ : R →+* A) ∧
        ∀ h : H, (s h : Matrix (Fin 4) (Fin 4) R).map φ = s' h

def IsLiftOnN (O : Type) [CommRing O] [IsLocalRing O] (n : ℕ) (H : Subgroup GQ)
    (c : Fin n → GQ → O) (A : Type) [CommRing A] [IsLocalRing A] [Algebra O A]
    (s : H →* GL (Fin n) A) : Prop :=
  (∀ m : ℕ, ∃ U : Subgroup GQ, IsOpen (U : Set GQ) ∧
    ∀ h : H, h.1 ∈ U → ∀ i j, ((s h : Matrix (Fin n) (Fin n) A) - 1) i j ∈ maximalIdeal A ^ m) ∧
  (∀ h : H, (s h : Matrix (Fin n) (Fin n) A).map (residue A) =
    (diagN c h).map (fun x => residue A (algebraMap O A x)))

def IsUnivLiftN (O : Type) [CommRing O] [IsLocalRing O] (n : ℕ) (H : Subgroup GQ)
    (c : Fin n → GQ → O) (P : ∀ (A : Type) [CommRing A] [IsLocalRing A] [Algebra O A],
      (H →* GL (Fin n) A) → Prop)
    (R : Type) [CommRing R] [IsLocalRing R] [Algebra O R] (s : H →* GL (Fin n) R) : Prop :=
  InCO O R ∧ IsLiftOnN O n H c R s ∧ P R s ∧
  ∀ (A : Type) [CommRing A] [IsLocalRing A] [Algebra O A], InCO O A →
    ∀ s' : H →* GL (Fin n) A, IsLiftOnN O n H c A s' → P A s' →
      ∃! φ : R →ₐ[O] A, IsLocalHom (φ : R →+* A) ∧
        ∀ h : H, (s h : Matrix (Fin n) (Fin n) R).map φ = s' h

def HasFlag {O : Type} [CommRing O] (H : Subgroup GQ) (I : Subgroup GQ) (c : Fin 4 → GQ → O)
    {R : Type} [CommRing R] [Algebra O R] (s : H →* GL (Fin 4) R) (K : Type) [Field K]
    (φ : R →+* K) : Prop :=
  ∃ g : GL (Fin 4) K,
    (∀ i j : Fin 4, i.val + j.val < 3 →
      ((g : Matrix (Fin 4) (Fin 4) K)ᵀ * Jsp4 K * (g : Matrix (Fin 4) (Fin 4) K)) i j = 0) ∧
    ∀ h : H,
      ((g⁻¹ : GL (Fin 4) K) * (s h : Matrix (Fin 4) (Fin 4) R).map φ *
        (g : Matrix (Fin 4) (Fin 4) K)).BlockTriangular id ∧
      (h.1 ∈ I → ∀ i : Fin 4,
        ((g⁻¹ : GL (Fin 4) K) * (s h : Matrix (Fin 4) (Fin 4) R).map φ *
          (g : Matrix (Fin 4) (Fin 4) K)) i i = φ (algebraMap O R (c i h)))

def IdY {O : Type} [CommRing O] (H I : Subgroup GQ) (c : Fin 4 → GQ → O) {R : Type} [CommRing R]
    [Algebra O R] (s : H →* GL (Fin 4) R) : Set R :=
  {x | ∀ (K : Type) [Field K] (φ : R →+* K), HasFlag H I c s K φ → φ x = 0}

def IsMinimalPrimeVanishingAtDiagonalPoints {O : Type} [CommRing O] (H I : Subgroup GQ) (c : Fin 4 → GQ → O) {R : Type}
    [CommRing R] [Algebra O R] (s : H →* GL (Fin 4) R) (P : Ideal R) : Prop :=
  P.IsPrime ∧ IdY H I c s ⊆ (P : Set R) ∧
  (∀ Q : Ideal R, Q.IsPrime → IdY H I c s ⊆ (Q : Set R) → Q ≤ P → Q = P) ∧
  ∀ φ₀ : R →ₐ[O] O, (∀ h : H, (s h : Matrix (Fin 4) (Fin 4) R).map φ₀ = diag4 c h) →
    P ≤ RingHom.ker φ₀

def LiesOnRt (O : Type) [CommRing O] [IsLocalRing O] (H I : Subgroup GQ) (ν : GQ → O)
    (c : Fin 4 → GQ → O) (A : Type) [CommRing A] [IsLocalRing A] [Algebra O A]
    (s' : H →* GL (Fin 4) A) : Prop :=
  ∀ (R : Type) [CommRing R] [IsLocalRing R] [Algebra O R] (s : H →* GL (Fin 4) R),
    IsUnivLift O H ν c (fun _ _ _ _ _ => True) R s →
    ∀ φ : R →ₐ[O] A, (∀ h : H, (s h : Matrix (Fin 4) (Fin 4) R).map φ = s' h) →
      ∀ P : Ideal R, IsMinimalPrimeVanishingAtDiagonalPoints H I c s P → ∀ x ∈ P, φ x = 0

def SuchCondRaw (D : XV) (plc : ℕ → ValuationSubring QbarQ) (l : ℕ) [Fact l.Prime] (O : Type)
    [CommRing O] [IsLocalRing O] (ν : GQ → O) (c : Fin 4 → GQ → O) (A : Type) [CommRing A]
    [IsLocalRing A] [Algebra O A] (r : (⊤ : Subgroup GQ) →* GL (Fin 4) A) : Prop :=
  (∀ q : ℕ, q.Prime → q ≠ l → q ∣ 2 * condV D → ∀ σ : (⊤ : Subgroup GQ),
    σ.1 ∈ Formalism.MainNotions.V.Lang.Ine (F := ℚ) (plc q) → (∀ i, residue O (c i σ) = 1) → r σ = 1) ∧
  (∀ q : ℕ, q.Prime → ¬ q ∣ 2 * l * condV D → ∀ σ : (⊤ : Subgroup GQ),
    σ.1 ∈ Formalism.MainNotions.V.Lang.Ine (F := ℚ) (plc q) → r σ = 1) ∧
  LiesOnRt O (Formalism.MainNotions.V.Lang.Dec (F := ℚ) (plc l)) (Formalism.MainNotions.V.Lang.Ine (F := ℚ) (plc l)) ν c A
    (r.comp (Subgroup.inclusion (le_top : Formalism.MainNotions.V.Lang.Dec (F := ℚ) (plc l) ≤ ⊤)))

def CharCoeffs {S : Type} [CommRing S] (ρ : (⊤ : Subgroup GQ) →* GL (Fin 4) S) : Set S :=
  {x | ∃ (g : (⊤ : Subgroup GQ)) (i : ℕ), x = (ρ g : Matrix (Fin 4) (Fin 4) S).charpoly.coeff i}

def SST (O : Type) [CommRing O] {S : Type} [CommRing S] [IsLocalRing S] [Algebra O S]
    (ρ : (⊤ : Subgroup GQ) →* GL (Fin 4) S) : Set S :=
  {x | ∀ n : ℕ, ∃ y ∈ Algebra.adjoin O (CharCoeffs ρ), x - y ∈ maximalIdeal S ^ n}

def torusEl3 {A : Type} [CommRing A] (t : Aˣ) : GL (Fin 3) A :=
  Units.map (Matrix.diagonalRingHom (Fin 3) A).toMonoidHom
    (MulEquiv.piUnits.symm (fun i : Fin 3 => ![t, 1, t⁻¹] i))

def IsCoef4Raw {l : ℕ} [Fact l.Prime] (Ol : Type) [CommRing Ol] (jO : Ol →+* QbarL l)
    (th ps al : GQ → QbarL l) (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [Algebra Ol O]
    (jO' : O →+* QbarL l) (c : Fin 4 → GQ → O) : Prop :=
  IsNoetherianRing O ∧ IsAdicComplete (maximalIdeal O) O ∧ Module.Finite Ol O ∧
  Function.Injective jO' ∧ jO'.comp (algebraMap Ol O) = jO ∧
  (∀ g, jO' (c 0 g) = th g) ∧ (∀ g, jO' (c 1 g) = ps g) ∧ (∀ g, jO' (c 2 g) = al g) ∧ (∀ g, c 3 g = 1)

def IsLift3 (O : Type) [CommRing O] [IsLocalRing O] (K : IntermediateField ℚ QbarQ) (cc : GQ)
    (c : Fin 3 → GQ → O) (A : Type) [CommRing A] [IsLocalRing A] [Algebra O A]
    (s : K.fixingSubgroup →* GL (Fin 3) A) : Prop :=
  IsLiftOnN O 3 K.fixingSubgroup c A s ∧
  ∀ g h : K.fixingSubgroup, (h : GQ) = cc * (g : GQ)⁻¹ * cc →
    (s h : Matrix (Fin 3) (Fin 3) A) = Jad3 A * (s g : Matrix (Fin 3) (Fin 3) A)ᵀ * Jad3 A

def IsPrimeRt3 {O : Type} [CommRing O] {l : ℕ} [Fact l.Prime] (j : O →+* QbarL l) (Gv : Subgroup GQ)
    (c : Fin 3 → GQ → O) (cr : (Gv →* GL (Fin 3) (QbarL l)) → Prop) {R : Type} [CommRing R]
    [Algebra O R] (s : Gv →* GL (Fin 3) R) (P : Ideal R) : Prop :=
  P.IsPrime ∧
  {x : R | ∀ ξ : R →+* QbarL l, ξ.comp (algebraMap O R) = j →
    cr ((Units.map (ξ.mapMatrix : Matrix (Fin 3) (Fin 3) R →+* Matrix (Fin 3) (Fin 3) (QbarL l)).toMonoidHom).comp s) →
    ξ x = 0} ⊆ (P : Set R) ∧
  (∀ Q : Ideal R, Q.IsPrime →
    {x : R | ∀ ξ : R →+* QbarL l, ξ.comp (algebraMap O R) = j →
      cr ((Units.map (ξ.mapMatrix : Matrix (Fin 3) (Fin 3) R →+* Matrix (Fin 3) (Fin 3) (QbarL l)).toMonoidHom).comp s) →
      ξ x = 0} ⊆ (Q : Set R) → Q ≤ P → Q = P) ∧
  ∀ φ₀ : R →ₐ[O] O, (∀ h : Gv, (s h : Matrix (Fin 3) (Fin 3) R).map φ₀ = diagN c h) →
    P ≤ RingHom.ker φ₀

def LiesOnRt3 (O : Type) [CommRing O] [IsLocalRing O] {l : ℕ} [Fact l.Prime] (j : O →+* QbarL l)
    (Gv : Subgroup GQ) (c : Fin 3 → GQ → O) (cr : (Gv →* GL (Fin 3) (QbarL l)) → Prop)
    (A : Type) [CommRing A] [IsLocalRing A] [Algebra O A] (s' : Gv →* GL (Fin 3) A) : Prop :=
  ∀ (R : Type) [CommRing R] [IsLocalRing R] [Algebra O R] (s : Gv →* GL (Fin 3) R),
    IsUnivLiftN O 3 Gv c (fun _ _ _ _ _ => True) R s →
    ∀ φ : R →ₐ[O] A, (∀ h : Gv, (s h : Matrix (Fin 3) (Fin 3) R).map φ = s' h) →
      ∀ P : Ideal R, IsPrimeRt3 j Gv c cr s P → ∀ x ∈ P, φ x = 0

noncomputable def etaK {O : Type} [CommRing O] (K : IntermediateField ℚ QbarQ) (g : GQ) : O :=
  open Classical in if g ∈ K.fixingSubgroup then 1 else -1

noncomputable def extendToGroupWithForm {O : Type} [CommRing O] (c : Fin 3 → GQ → O) (K : IntermediateField ℚ QbarQ)
    (cc : GQ) (g : GQ) : Matrix (Fin 3) (Fin 3) O :=
  open Classical in
  if g ∈ K.fixingSubgroup then diagN c g else diagN c (g * cc) * Jad3 O

open Classical in

noncomputable def extGG3 {A : Type} [CommRing A] (K : IntermediateField ℚ QbarQ) (cc : GQ)
    (H : Subgroup GQ) (s : K.fixingSubgroup →* GL (Fin 3) A) (g : H) : Matrix (Fin 3) (Fin 3) A :=
  if h : (g : GQ) ∈ K.fixingSubgroup then (s ⟨g, h⟩ : Matrix (Fin 3) (Fin 3) A)
  else if h' : (g : GQ) * cc ∈ K.fixingSubgroup then
    (s ⟨(g : GQ) * cc, h'⟩ : Matrix (Fin 3) (Fin 3) A) * Jad3 A
  else 0

open Classical in

def IsLiftGG3 (O : Type) [CommRing O] [IsLocalRing O] (H GK : Subgroup GQ) (η : GQ → O)
    (c0 : GQ → Matrix (Fin 3) (Fin 3) O) (A : Type) [CommRing A] [IsLocalRing A] [Algebra O A]
    (r : H → Matrix (Fin 3) (Fin 3) A) : Prop :=
  (∀ g, IsUnit (r g).det) ∧
  (∀ g h : H, r (g * h) = r g * (if (g : GQ) ∈ GK then r h else
    algebraMap O A (η h) • ((r h)⁻¹)ᵀ)) ∧
  (∀ m : ℕ, ∃ U : Subgroup GQ, IsOpen (U : Set GQ) ∧
    ∀ h : H, h.1 ∈ U → ∀ i j, (r h - 1) i j ∈ maximalIdeal A ^ m) ∧
  (∀ h : H, (r h).map (residue A) = (c0 h).map (fun x => residue A (algebraMap O A x)))

open Classical in

def IsUnivLiftGG3 (O : Type) [CommRing O] [IsLocalRing O] (H GK : Subgroup GQ) (η : GQ → O)
    (c0 : GQ → Matrix (Fin 3) (Fin 3) O)
    (P : ∀ (A : Type) [CommRing A] [IsLocalRing A] [Algebra O A], (H → Matrix (Fin 3) (Fin 3) A) → Prop)
    (R : Type) [CommRing R] [IsLocalRing R] [Algebra O R] (s : H → Matrix (Fin 3) (Fin 3) R) : Prop :=
  InCO O R ∧ IsLiftGG3 O H GK η c0 R s ∧ P R s ∧
  ∀ (A : Type) [CommRing A] [IsLocalRing A] [Algebra O A], InCO O A →
    ∀ s' : H → Matrix (Fin 3) (Fin 3) A, IsLiftGG3 O H GK η c0 A s' → P A s' →
      ∃! φ : R →ₐ[O] A, IsLocalHom (φ : R →+* A) ∧ ∀ h : H, (s h).map φ = s' h

def CrOnGK {l : ℕ} [Fact l.Prime] (H GK : Subgroup GQ)
    (cr : ((H ⊓ GK : Subgroup GQ) →* GL (Fin 3) (QbarL l)) → Prop)
    (f : H → Matrix (Fin 3) (Fin 3) (QbarL l)) : Prop :=
  ∃ ρ : (H ⊓ GK : Subgroup GQ) →* GL (Fin 3) (QbarL l),
    (∀ g : (H ⊓ GK : Subgroup GQ), (ρ g : Matrix (Fin 3) (Fin 3) (QbarL l)) = f ⟨g, g.2.1⟩) ∧ cr ρ

def IsPrimeRtGG3 {O : Type} [CommRing O] {l : ℕ} [Fact l.Prime] (j : O →+* QbarL l) (H GK : Subgroup GQ)
    (c0 : GQ → Matrix (Fin 3) (Fin 3) O)
    (cr : ((H ⊓ GK : Subgroup GQ) →* GL (Fin 3) (QbarL l)) → Prop) {R : Type} [CommRing R]
    [Algebra O R] (s : H → Matrix (Fin 3) (Fin 3) R) (P : Ideal R) : Prop :=
  P.IsPrime ∧
  {x : R | ∀ ξ : R →+* QbarL l, ξ.comp (algebraMap O R) = j →
    CrOnGK H GK cr (fun g => (s g).map ξ) → ξ x = 0} ⊆ (P : Set R) ∧
  (∀ Q : Ideal R, Q.IsPrime →
    {x : R | ∀ ξ : R →+* QbarL l, ξ.comp (algebraMap O R) = j →
      CrOnGK H GK cr (fun g => (s g).map ξ) → ξ x = 0} ⊆ (Q : Set R) → Q ≤ P → Q = P) ∧
  ∀ φ₀ : R →ₐ[O] O, (∀ h : H, (s h).map φ₀ = c0 h) → P ≤ RingHom.ker φ₀

def LiesOnRtGG3 (O : Type) [CommRing O] [IsLocalRing O] {l : ℕ} [Fact l.Prime] (j : O →+* QbarL l)
    (H GK : Subgroup GQ) (η : GQ → O) (c0 : GQ → Matrix (Fin 3) (Fin 3) O)
    (cr : ((H ⊓ GK : Subgroup GQ) →* GL (Fin 3) (QbarL l)) → Prop)
    (A : Type) [CommRing A] [IsLocalRing A] [Algebra O A] (s' : H → Matrix (Fin 3) (Fin 3) A) : Prop :=
  ∀ (R : Type) [CommRing R] [IsLocalRing R] [Algebra O R] (s : H → Matrix (Fin 3) (Fin 3) R),
    IsUnivLiftGG3 O H GK η c0 (fun _ _ _ _ _ => True) R s →
    ∀ φ : R →ₐ[O] A, (∀ h : H, (s h).map φ = s' h) →
      ∀ P : Ideal R, IsPrimeRtGG3 j H GK c0 cr s P → ∀ x ∈ P, φ x = 0

structure NormEqs3 (O : Type) [CommRing O] where
  ι : Type
  [fin : Fintype ι]
  g : ι → GQ
  h : ι → GQ
  a : ι → O
  b : ι → O
  i : ι → Fin 3
  j : ι → Fin 3
  off : ∀ k, i k ≠ j k

def IsNormalizedUnitaryLift {O : Type} [CommRing O] (K : IntermediateField ℚ QbarQ) (E : NormEqs3 O)
    (A : Type) [CommRing A] [Algebra O A] (s : K.fixingSubgroup →* GL (Fin 3) A) : Prop :=
  ∀ (k : E.ι) (x y : K.fixingSubgroup), (x : GQ) = E.g k → (y : GQ) = E.h k →
    (algebraMap O A (E.a k) • (s x : Matrix (Fin 3) (Fin 3) A) +
      algebraMap O A (E.b k) • (s y : Matrix (Fin 3) (Fin 3) A)) (E.i k) (E.j k) = 0

def normEquationsThree (O : Type) [CommRing O] (g1 cc : GQ) : NormEqs3 O where
  ι := Bool
  g := fun _ => g1
  h := fun _ => cc * g1⁻¹ * cc
  a := fun _ => 1
  b := fun _ => -1
  i := fun k => if k then 0 else 1
  j := fun k => if k then 1 else 0
  off := fun k => by cases k <;> decide

def CrSt {l : ℕ} [Fact l.Prime] (q0 : ℕ) (phiW : GQ) (H GK I : Subgroup GQ)
    (ρ : (H ⊓ GK : Subgroup GQ) →* GL (Fin 3) (QbarL l)) : Prop :=
  (∀ g : (H ⊓ GK : Subgroup GQ), (g : GQ) = phiW → ∃ u : QbarL l,
    (ρ g : Matrix (Fin 3) (Fin 3) (QbarL l)).charpoly =
      (Polynomial.X - Polynomial.C ((q0 : QbarL l) * u)) * (Polynomial.X - Polynomial.C u) *
        (Polynomial.X - Polynomial.C (u / (q0 : QbarL l)))) ∧
  ∀ σ : (H ⊓ GK : Subgroup GQ), (σ : GQ) ∈ I → ((ρ σ : Matrix (Fin 3) (Fin 3) (QbarL l)) - 1) ^ 3 = 0

def Cond3Raw (N : ℕ) (plc : ℕ → ValuationSubring QbarQ) (l : ℕ) [Fact l.Prime] (cc : GQ) (q0 : ℕ) (phiW : GQ)
    (K : IntermediateField ℚ QbarQ) (O : Type) [CommRing O] [IsLocalRing O] (j : O →+* QbarL l)
    (nrm : NormEqs3 O) (c : Fin 3 → GQ → O)
    (cr : ((Formalism.MainNotions.V.Lang.Dec (F := ℚ) (plc l) ⊓ K.fixingSubgroup : Subgroup GQ) →* GL (Fin 3) (QbarL l)) → Prop)
    (A : Type) [CommRing A] [IsLocalRing A] [Algebra O A] (s : K.fixingSubgroup →* GL (Fin 3) A) : Prop :=
  IsNormalizedUnitaryLift K nrm A s ∧
  (∀ q : ℕ, q.Prime → q ≠ l →
    (q ∣ N ∨ ¬ Formalism.MainNotions.V.Lang.Ine (F := ℚ) (plc q) ≤ K.fixingSubgroup) →
    ∀ σ : K.fixingSubgroup, (σ : GQ) ∈ Formalism.MainNotions.V.Lang.Ine (F := ℚ) (plc q) →
      (∀ i, residue O (c i σ) = 1) → s σ = 1) ∧
  (∀ q : ℕ, q.Prime → q ≠ l → q ≠ q0 → ¬ q ∣ N →
    Formalism.MainNotions.V.Lang.Ine (F := ℚ) (plc q) ≤ K.fixingSubgroup →
    ∀ σ : K.fixingSubgroup, (σ : GQ) ∈ Formalism.MainNotions.V.Lang.Ine (F := ℚ) (plc q) → s σ = 1) ∧
  LiesOnRtGG3 O j (Formalism.MainNotions.V.Lang.Dec (F := ℚ) (plc l)) K.fixingSubgroup (fun _ => 1) (extendToGroupWithForm c K cc) cr A
    (extGG3 K cc (Formalism.MainNotions.V.Lang.Dec (F := ℚ) (plc l)) s) ∧
  (q0.Prime → LiesOnRtGG3 O j (Formalism.MainNotions.V.Lang.Dec (F := ℚ) (plc q0)) K.fixingSubgroup (fun _ => 1) (extendToGroupWithForm c K cc)
    (CrSt q0 phiW (Formalism.MainNotions.V.Lang.Dec (F := ℚ) (plc q0)) K.fixingSubgroup (Formalism.MainNotions.V.Lang.Ine (F := ℚ) (plc q0))) A
    (extGG3 K cc (Formalism.MainNotions.V.Lang.Dec (F := ℚ) (plc q0)) s))

def Tri3Raw {O : Type} [CommRing O] {l : ℕ} [Fact l.Prime] (j : O →+* QbarL l) (psi : Fin 3 → GQ → O)
    (D I GK : Subgroup GQ) (ρ : (D ⊓ GK : Subgroup GQ) →* GL (Fin 3) (QbarL l)) (Q : GL (Fin 3) (QbarL l)) :
    Prop :=
  (∀ g : (D ⊓ GK : Subgroup GQ), (Q⁻¹.1 * (ρ g).1 * Q.1).BlockTriangular id) ∧
  ∀ σ : (D ⊓ GK : Subgroup GQ), (σ : GQ) ∈ I → ∀ i : Fin 3, (Q⁻¹.1 * (ρ σ).1 * Q.1) i i = j (psi i σ)

def Ord3Raw {O : Type} [CommRing O] {l : ℕ} [Fact l.Prime] (j : O →+* QbarL l) (psi : Fin 3 → GQ → O)
    (D I GK : Subgroup GQ) (ρ : (D ⊓ GK : Subgroup GQ) →* GL (Fin 3) (QbarL l)) : Prop :=
  ∃ Q : GL (Fin 3) (QbarL l), Tri3Raw j psi D I GK ρ Q ∧
    (∃ g : (D ⊓ GK : Subgroup GQ), (Q⁻¹.1 * (ρ g).1 * Q.1) 0 0 ≠
      ((epsL l (g : GQ) : (QbarL l)ˣ) : QbarL l) * (Q⁻¹.1 * (ρ g).1 * Q.1) 1 1) ∧
    ∃ g : (D ⊓ GK : Subgroup GQ), (Q⁻¹.1 * (ρ g).1 * Q.1) 1 1 ≠
      ((epsL l (g : GQ) : (QbarL l)ˣ) : QbarL l) * (Q⁻¹.1 * (ρ g).1 * Q.1) 2 2

def HcrSub (l : ℕ) [Fact l.Prime] (a : ℕ) (H : Subgroup GQ) : Subgroup GQ :=
  H ⊓ ((powMonoidHom a).comp (Formalism.MainNotions.V.Lang.cycMod ℚ QbarQ l 1)).ker

def IsNorm4 {O : Type} [CommRing O] (c : Fin 4 → GQ → O) (ph g : GQ) (A : Type) [CommRing A]
    [Algebra O A] (r : (⊤ : Subgroup GQ) →* GL (Fin 4) A) : Prop :=
  (∀ i j : Fin 4, i.val % 2 ≠ j.val % 2 →
    (r ⟨ph, Subgroup.mem_top ph⟩ : Matrix (Fin 4) (Fin 4) A) i j = 0) ∧
  ((r ⟨g, Subgroup.mem_top g⟩ : Matrix (Fin 4) (Fin 4) A) +
    algebraMap O A (c 0 g) • ((r ⟨g, Subgroup.mem_top g⟩)⁻¹ : GL (Fin 4) A).1) 0 2 = 0 ∧
  ((r ⟨g, Subgroup.mem_top g⟩ : Matrix (Fin 4) (Fin 4) A) +
    algebraMap O A (c 0 g) • ((r ⟨g, Subgroup.mem_top g⟩)⁻¹ : GL (Fin 4) A).1) 2 0 = 0

def IsWt3 (O : Type) [CommRing O] [IsLocalRing O] {K : IntermediateField ℚ QbarQ} {R : Type}
    [CommRing R] [Algebra O R] (r : K.fixingSubgroup →* GL (Fin 3) R) (j : ℤ) (y : R) : Prop :=
  ∀ (A : Type) [CommRing A] [IsLocalRing A] [Algebra O A], InCO O A → ∀ (t : Aˣ) (φ φt : R →ₐ[O] A),
    (∀ g : K.fixingSubgroup, (r g : Matrix (Fin 3) (Fin 3) R).map φt =
      ((torusEl3 t : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A) * (r g : Matrix (Fin 3) (Fin 3) R).map φ *
        (((torusEl3 t)⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A)) →
    φt y = ((t ^ j : Aˣ) : A) * φ y

def torusElG {A : Type} [CommRing A] (s t : Aˣ) : GL (Fin 4) A :=
  Units.map (Matrix.diagonalRingHom (Fin 4) A).toMonoidHom
    (MulEquiv.piUnits.symm (fun i : Fin 4 => ![s * t, t, s, 1] i))

def IsWt4 (O : Type) [CommRing O] [IsLocalRing O] {R : Type} [CommRing R] [Algebra O R]
    (r : (⊤ : Subgroup GQ) →* GL (Fin 4) R) (j : Fin 2 → ℤ) (y : R) : Prop :=
  ∀ (A : Type) [CommRing A] [IsLocalRing A] [Algebra O A], InCO O A → ∀ (s t : Aˣ) (φ φt : R →ₐ[O] A),
    (∀ g : (⊤ : Subgroup GQ), (r g : Matrix (Fin 4) (Fin 4) R).map φt =
      ((torusElG s t : GL (Fin 4) A) : Matrix (Fin 4) (Fin 4) A) * (r g : Matrix (Fin 4) (Fin 4) R).map φ *
        (((torusElG s t)⁻¹ : GL (Fin 4) A) : Matrix (Fin 4) (Fin 4) A)) →
    φt y = ((s ^ j 0 * t ^ j 1 : Aˣ) : A) * φ y

end univ

def IsPrimeToL (l : ℕ) (x : GQ) : Prop :=
  ∀ U : Subgroup GQ, IsOpen (U : Set GQ) → ∃ m : ℕ, 0 < m ∧ ¬ l ∣ m ∧ x ^ m ∈ U

def IsProL (l : ℕ) (x : GQ) : Prop :=
  ∀ U : Subgroup GQ, IsOpen (U : Set GQ) → ∃ k : ℕ, x ^ (l ^ k) ∈ U

def IsNormDataRaw (A : ValuationSubring QbarQ) (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O]
    [IsLocalRing O] (c : Fin 4 → GQ → O) (ph g : GQ) : Prop :=
  (∃ φ u : GQ, Formalism.ConjugateSelfDual.IsFrob (F := ℚ) A l φ ∧
    PadicInt.toZMod ((eps l φ : ℤ_[l]ˣ) : ℤ_[l]) = 1 ∧
    φ = ph * u ∧ Commute ph u ∧ IsPrimeToL l ph ∧ IsProL l u) ∧
  IsLocalRing.residue O (c 2 g) ≠ 1 ∧ IsLocalRing.residue O (c 1 g) ≠ 1

end TV

namespace VH

open IsDedekindDomain

def qmap {T : Type*} [CommGroup T] {F F' : Subgroup T} (h : F ≤ F') : T ⧸ F →* T ⧸ F' :=
  QuotientGroup.map F F' (MonoidHom.id T) h

def abelian₂ (O : Type*) [CommRing O] {T : Type*} [CommGroup T] (fil : ℕ → Subgroup T) (h : Antitone fil) :
    Subalgebra O (∀ b, MonoidAlgebra O (T ⧸ fil b)) :=
  ⨅ b, AlgHom.equalizer
    ((MonoidAlgebra.mapDomainAlgHom O O (qmap (h (Nat.le_succ b)))).comp (Pi.evalAlgHom O _ (b + 1)))
    (Pi.evalAlgHom O _ b)

inductive HCase
  |   U
  |   D
  deriving DecidableEq

abbrev Lp (L : Type) [Field L] : Type := ↥(NumberField.maximalRealSubfield L)

def resPL (L : Type) [Field L] [NumberField L] [Algebra L TV.QbarQ] :
    Formalism.ConjugateSelfDual.G L TV.QbarQ →* Formalism.ConjugateSelfDual.G (Lp L) TV.QbarQ where
  toFun g := g.restrictScalars (Lp L)
  map_one' := rfl
  map_mul' _ _ := rfl

def resQL (L : Type) [Field L] [NumberField L] [Algebra L TV.QbarQ] :
    Formalism.ConjugateSelfDual.G L TV.QbarQ →* Formalism.ConjugateSelfDual.G ℚ TV.QbarQ where
  toFun g := g.restrictScalars ℚ
  map_one' := rfl
  map_mul' _ _ := rfl

structure HidaSetting where
  case : HCase

  n : ℕ
  n_pos : 0 < n
  n_D : case = .D → n = 2

  l : ℕ
  [hl : Fact l.Prime]
  l_odd : l ≠ 2

  O : Type
  [instO : CommRing O] [instOdom : IsDomain O] [instOloc : IsLocalRing O] [instOalg : Algebra ℤ_[l] O]
  [instOfin : Module.Finite ℤ_[l] O]
  [instOQ : Algebra O (TV.QbarL l)]
  OQ_inj : Function.Injective (algebraMap O (TV.QbarL l))

  OQ_zp : ∀ x : ℤ_[l], algebraMap O (TV.QbarL l) (algebraMap ℤ_[l] O x) =
    algebraMap ℚ_[l] (TV.QbarL l) (x : ℚ_[l])

  L : Type
  [instL : Field L] [instLnf : NumberField L] [instLQ : Algebra L TV.QbarQ]
  [instLac : IsAlgClosure L TV.QbarQ]

  Fp : Subfield L

  TT : Type
  [instTT : CommGroup TT]
  fil : ℕ → Subgroup TT
  fil_anti : Antitone fil
  fil_fin : ∀ b, (fil b).FiniteIndex

  t0 : TT → Oˣ
  torsion_character_mul : ∀ s t, IsOfFinOrder s → IsOfFinOrder t → t0 (s * t) = t0 s * t0 t

  Vl : Type
  [instVl : Fintype Vl]
  vt : Vl → HeightOneSpectrum (𝓞 L)

  ej : ∀ v : Vl, Fin n → (HeightOneSpectrum.adicCompletionIntegers L (vt v))ˣ →* TT

  At : Vl → ValuationSubring TV.QbarQ
  At_over : ∀ v, Formalism.ConjugateSelfDual.IsPlaceOver (F := L) (At v) (vt v)

  unif : ∀ v : Vl, (HeightOneSpectrum.adicCompletion L (vt v))ˣ
  unif_val : ∀ v, Valued.v ((unif v : HeightOneSpectrum.adicCompletion L (vt v))) =
    ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))

  Wsp : Type
  wsp : Wsp → HeightOneSpectrum (𝓞 L)

  [instOdvr : IsDiscreteValuationRing O]

  Fp_eq : Fp = NumberField.maximalRealSubfield L
  cm_U : case = .U → NumberField.IsCMField L
  real_D : case = .D → NumberField.IsTotallyReal L ∧ Even (Module.finrank ℚ L)

  wl : Vl → HeightOneSpectrum (𝓞 (Lp L))
  wl_over : ∀ v, Formalism.ConjugateSelfDual.IsPlaceOver (F := Lp L) (At v) (wl v)
  wl_inj : Function.Injective wl
  wl_range : ∀ w, w ∈ Set.range wl ↔ ((l : ℤ) : 𝓞 (Lp L)) ∈ w.asIdeal

  St : Finset (HeightOneSpectrum (𝓞 (Lp L)))
  St_l : ∀ u ∈ St, ((l : ℤ) : 𝓞 (Lp L)) ∉ u.asIdeal
  Au : St → ValuationSubring TV.QbarQ
  Au_over : ∀ u, Formalism.ConjugateSelfDual.IsPlaceOver (F := Lp L) (Au u) u.1

  v0 : HeightOneSpectrum (𝓞 (Lp L))
  A0 : ValuationSubring TV.QbarQ
  auxiliary_place_over : Formalism.ConjugateSelfDual.IsPlaceOver (F := Lp L) A0 v0
  p0 : ℕ
  auxiliary_prime_prime : p0.Prime
  auxiliary_prime_odd_alt : p0 ≠ 2
  auxiliary_prime_ne : p0 ≠ l
  p0_mem : ((p0 : ℤ) : 𝓞 (Lp L)) ∈ v0.asIdeal
  auxiliary_place_norm : Formalism.ConjugateSelfDual.normV v0 = p0
  auxiliary_prime_unramified : ∀ A : ValuationSubring TV.QbarQ, A.valuation ((p0 : ℚ) : TV.QbarQ) < 1 →
    Formalism.MainNotions.V.Lang.Ine (F := ℚ) A ≤ (resQL L).range
  v0_St : v0 ∉ St

  unram : case = .U → ∀ A : ValuationSubring TV.QbarQ, Formalism.MainNotions.V.Lang.IsFinitePlace (Lp L) A →
    Formalism.MainNotions.V.Lang.Ine (F := Lp L) A ≤ (resPL L).range

  split : case = .U → ∀ (v : HeightOneSpectrum (𝓞 (Lp L))) (A : ValuationSubring TV.QbarQ),
    (((l : ℤ) : 𝓞 (Lp L)) ∈ v.asIdeal ∨ v ∈ St ∨ v = v0) → Formalism.ConjugateSelfDual.IsPlaceOver (F := Lp L) A v →
    Formalism.MainNotions.V.Lang.Dec (F := Lp L) A ≤ (resPL L).range

  c : Formalism.ConjugateSelfDual.G (Lp L) TV.QbarQ
  c_cc : Formalism.MainNotions.V.Lang.IsCC c

  tau : ∀ u : St, Formalism.MainNotions.V.Lang.Ine (F := L) (Au u) →* GL (Fin n) O
  tau_fin : ∀ u, Finite (tau u).range
  tau_prime : ∀ u, Nat.Coprime (Nat.card (tau u).range) l
  tau_cont : ∀ u, @Continuous _ _ _ ⊥ (tau u)

  nuG : Formalism.ConjugateSelfDual.G L TV.QbarQ →* Oˣ
  mD : ℤ

  nu_I : case = .D → ∀ v : Vl, ∃ k : ℕ, 0 < k ∧ ∀ g ∈ Formalism.MainNotions.V.Lang.Ine (F := L) (At v),
    (nuG g * ((Units.map (algebraMap ℤ_[l] O).toMonoidHom (Formalism.MainNotions.V.Lang.cycZ L TV.QbarQ l g)) ^ mD)⁻¹) ^ k = 1

  nu_unr : case = .D → ∀ A : ValuationSubring TV.QbarQ, Formalism.MainNotions.V.Lang.IsFinitePlace L A →
    (∀ v : HeightOneSpectrum (𝓞 (Lp L)), Formalism.ConjugateSelfDual.IsPlaceOver (F := Lp L) A v →
      ¬ (((l : ℤ) : 𝓞 (Lp L)) ∈ v.asIdeal ∨ v ∈ St)) →
    ∀ σ ∈ Formalism.MainNotions.V.Lang.Ine (F := L) A, nuG σ = 1

  tau_det : case = .D → ∀ (u : St) (g : Formalism.MainNotions.V.Lang.Ine (F := L) (Au u)),
    ((tau u g : GL (Fin n) O) : Matrix (Fin n) (Fin n) O).det = ((nuG g : Oˣ) : O)

  ttU : case = .U → Function.Bijective (fun t : (∀ v : Vl, Fin n → (HeightOneSpectrum.adicCompletionIntegers L (vt v))ˣ) =>
    ∏ v, ∏ j, ej v j (t v j))

  ttD : case = .D → Function.Bijective (fun t : (∀ v : Vl, (HeightOneSpectrum.adicCompletionIntegers L (vt v))ˣ) =>
    ∏ v, ej v ⟨0, n_pos⟩ (t v))
  ejD : case = .D → ∀ v (j : Fin n) x, (j : ℕ) = 1 → ej v j x = (ej v ⟨0, n_pos⟩ x)⁻¹

  fil_gen : ∀ b : ℕ, fil b = Subgroup.closure {t | ∃ (v : Vl) (j : Fin n)
    (x : (HeightOneSpectrum.adicCompletionIntegers L (vt v))ˣ),
    ((x : HeightOneSpectrum.adicCompletionIntegers L (vt v)) - 1 ∈
        IsLocalRing.maximalIdeal (HeightOneSpectrum.adicCompletionIntegers L (vt v)) ^ b) ∧ t = ej v j x}

  wsp_spec : Function.Injective wsp ∧
    ∀ w : HeightOneSpectrum (𝓞 L), w ∈ Set.range wsp ↔
      ∀ A : ValuationSubring TV.QbarQ, Formalism.ConjugateSelfDual.IsPlaceOver (F := L) A w →
        (Formalism.MainNotions.V.Lang.IsFinitePlace (Lp L) A ∧ ∀ v : HeightOneSpectrum (𝓞 (Lp L)),
          Formalism.ConjugateSelfDual.IsPlaceOver (F := Lp L) A v → ¬ (((l : ℤ) : 𝓞 (Lp L)) ∈ v.asIdeal ∨ v ∈ St ∨ v = v0)) ∧
        (case = .U → Formalism.MainNotions.V.Lang.Dec (F := Lp L) A ≤ (resPL L).range)

attribute [instance] HidaSetting.hl HidaSetting.instO HidaSetting.instOdom HidaSetting.instOloc HidaSetting.instOalg
  HidaSetting.instOfin HidaSetting.instOQ HidaSetting.instL HidaSetting.instLnf HidaSetting.instLQ HidaSetting.instLac HidaSetting.instOdvr HidaSetting.instTT
  HidaSetting.instVl

namespace HidaSetting

variable (s : HidaSetting)

def NoZeta : Prop := ∀ ζ : s.L, ¬ IsPrimitiveRoot ζ s.l

abbrev Lamf : Type := VH.abelian₂ s.O s.fil s.fil_anti

instance : CommRing s.Lamf := inferInstance

instance : Algebra s.O s.Lamf := inferInstance

def brk (t : s.TT) : s.Lamf :=
  ⟨fun b => MonoidAlgebra.of s.O _ (t : s.TT ⧸ s.fil b), by
    rw [VH.abelian₂, Algebra.mem_iInf]
    intro b
    rw [AlgHom.mem_equalizer]
    simp [qmap, MonoidAlgebra.mapDomainAlgHom, MonoidAlgebra.of_apply, MonoidAlgebra.mapDomain_single]
    rfl⟩

def torsionIdealAlt : Ideal s.Lamf :=
  Ideal.span {x | ∃ t : s.TT, IsOfFinOrder t ∧ x = s.brk t - algebraMap s.O s.Lamf (s.t0 t : s.O)}

abbrev abelian₂ : Type := s.Lamf ⧸ s.torsionIdealAlt

instance : CommRing s.abelian₂ := Ideal.Quotient.commRing _

instance : Algebra s.Lamf s.abelian₂ := Ideal.Quotient.algebra _

instance : Module s.Lamf s.abelian₂ := Algebra.toModule

abbrev GL_ : Type := Formalism.ConjugateSelfDual.G s.L TV.QbarQ

abbrev Gv (v : s.Vl) : Subgroup s.GL_ := Formalism.MainNotions.V.Lang.Dec (F := s.L) (s.At v)

abbrev Iv (v : s.Vl) : Subgroup s.GL_ := Formalism.MainNotions.V.Lang.Ine (F := s.L) (s.At v)

def unitIncl (v : s.Vl) : (HeightOneSpectrum.adicCompletionIntegers s.L (s.vt v))ˣ →*
    (HeightOneSpectrum.adicCompletion s.L (s.vt v))ˣ :=
  Units.map (HeightOneSpectrum.adicCompletionIntegers s.L (s.vt v)).subtype.toMonoidHom

abbrev ArtAt : Type := ∀ v : s.Vl, (HeightOneSpectrum.adicCompletion s.L (s.vt v))ˣ →* Abelianization (s.Gv v)

end HidaSetting

structure Sys (s : HidaSetting) where

  Mf : Type
  [instMf : AddCommGroup Mf]
  [instMfL : Module s.Lamf Mf]

  Tbig : Type
  [instT : CommRing Tbig]
  [instTL : Algebra s.abelian₂ Tbig]

  act : Tbig →ₐ[s.abelian₂] Module.End s.abelian₂ (TensorProduct s.Lamf s.abelian₂ Mf)
  act_inj : Function.Injective act

  Tw : s.Wsp → Fin (s.n + 1) → Tbig
  TwInv : s.Wsp → Tbig
  TwInv_spec : ∀ w, TwInv w * Tw w (Fin.last s.n) = 1
  u : s.Vl → Fin s.n → Tbig

  gen : Algebra.adjoin s.abelian₂ (Set.range (fun p : s.Wsp × Fin (s.n + 1) => Tw p.1 p.2) ∪ Set.range TwInv ∪
    Set.range (fun p : s.Vl × Fin s.n => u p.1 p.2)) = ⊤

attribute [instance] Sys.instMf Sys.instMfL Sys.instT Sys.instTL

namespace Sys

variable {s : HidaSetting} (H : Sys s)

abbrev MfL : Type := TensorProduct s.Lamf s.abelian₂ H.Mf

instance (priority := 2000) instTbigMfL : Module H.Tbig H.MfL := Module.compHom H.MfL H.act.toRingHom

instance (priority := 2000) instTbigMfLD : DistribMulAction H.Tbig H.MfL := (instTbigMfL H).toDistribMulAction

abbrev T (mm : Ideal H.Tbig) [mm.IsMaximal] : Type := Localization.AtPrime mm

abbrev M (mm : Ideal H.Tbig) [mm.IsMaximal] : Type := LocalizedModule mm.primeCompl H.MfL

def zT (mm : Ideal H.Tbig) [mm.IsMaximal] : ℤ_[s.l] →+* H.T mm :=
  (algebraMap H.Tbig (H.T mm)).comp ((algebraMap s.abelian₂ H.Tbig).comp ((algebraMap s.Lamf s.abelian₂).comp
    ((algebraMap s.O s.Lamf).comp (algebraMap ℤ_[s.l] s.O))))

def oT (mm : Ideal H.Tbig) [mm.IsMaximal] : s.O →+* H.T mm :=
  (algebraMap H.Tbig (H.T mm)).comp ((algebraMap s.abelian₂ H.Tbig).comp ((algebraMap s.Lamf s.abelian₂).comp
    (algebraMap s.O s.Lamf)))

def epsT (mm : Ideal H.Tbig) [mm.IsMaximal] (v : s.Vl) (j : Fin s.n) :
    Abelianization (s.Gv v) →* (H.T mm)ˣ :=
  Abelianization.lift (((Units.map (H.zT mm).toMonoidHom).comp
    ((Formalism.MainNotions.V.Lang.cycZ s.L TV.QbarQ s.l).comp (s.Gv v).subtype)) ^ (1 - ((j : ℕ) + 1 : ℤ)))

def brkT (mm : Ideal H.Tbig) [mm.IsMaximal] (t : s.TT) : H.T mm :=
  algebraMap H.Tbig (H.T mm) (algebraMap s.abelian₂ H.Tbig (algebraMap s.Lamf s.abelian₂ (s.brk t)))

def uT (mm : Ideal H.Tbig) [mm.IsMaximal] (v : s.Vl) (j : Fin s.n) : H.T mm :=
  algebraMap H.Tbig (H.T mm) (H.u v j)

end Sys

structure Loc {s : HidaSetting} (H : Sys s) (mm : Ideal H.Tbig) [mm.IsMaximal] (art : s.ArtAt) where
  psi : ∀ (v : s.Vl) (j : Fin s.n), s.Gv v →* (H.T mm)ˣ

  psi_unit : ∀ v j (x : (HeightOneSpectrum.adicCompletionIntegers s.L (s.vt v))ˣ),
    ((Abelianization.lift (psi v j) (art v (s.unitIncl v x)) : (H.T mm)ˣ) : H.T mm) *
        H.brkT mm (s.ej v j x) *
        (if s.case = .D ∧ (j : ℕ) = 1 then
          H.oT mm (((Abelianization.lift (s.nuG.comp (s.Gv v).subtype) (art v (s.unitIncl v x)))⁻¹ : s.Oˣ) : s.O)
        else 1) =
      ((H.epsT mm v j (art v (s.unitIncl v x)) : (H.T mm)ˣ) : H.T mm)

  psi_unif : ∀ v j,
    ((Abelianization.lift (psi v j) (art v (s.unif v)) : (H.T mm)ˣ) : H.T mm) =
      ((H.epsT mm v j (art v (s.unif v)) : (H.T mm)ˣ) : H.T mm) * H.uT mm v j

  rx : (H.T mm →+* TV.QbarL s.l) → (s.GL_ →* GL (Fin s.n) (TV.QbarL s.l))

namespace HidaSetting

variable (s : HidaSetting)

abbrev kk : Type := IsLocalRing.ResidueField s.O

def epsO : s.GL_ →* s.Oˣ :=
  (Units.map (algebraMap ℤ_[s.l] s.O).toMonoidHom).comp (Formalism.MainNotions.V.Lang.cycZ s.L TV.QbarQ s.l)

def omk : s.GL_ →* s.kkˣ := (Units.map (IsLocalRing.residue s.O).toMonoidHom).comp s.epsO

def conjL (g : s.GL_) : s.GL_ := by
  classical
  exact if h : ∃ h', resPL s.L h' = s.c * resPL s.L g * s.c⁻¹ then h.choose else 1

def epsPow (g : s.GL_) : s.Oˣ := s.epsO g ^ (1 - (s.n : ℤ))

def starEl {R : Type} [CommRing R] (ι : s.O →+* R) (x : MonoidAlgebra R s.GL_) : MonoidAlgebra R s.GL_ :=
  x.coeff.sum (fun g a => MonoidAlgebra.single (s.conjL g)⁻¹ (a * ι (s.epsPow g : s.O)))

def diagRep {G R : Type} [Group G] [CommRing R] {m : ℕ} (χ : Fin m → G →* Rˣ) :
    G →* Matrix (Fin m) (Fin m) R where
  toFun g := Matrix.diagonal (fun i => ((χ i g : Rˣ) : R))
  map_one' := by simp
  map_mul' a b := by simp [Matrix.diagonal_mul_diagonal]

def InS (v : HeightOneSpectrum (𝓞 (Lp s.L))) : Prop :=
  ((s.l : ℤ) : 𝓞 (Lp s.L)) ∈ v.asIdeal ∨ v ∈ s.St ∨ v = s.v0

def OutS (S' : Set (HeightOneSpectrum (𝓞 (Lp s.L)))) (A : ValuationSubring TV.QbarQ) : Prop :=
  Formalism.MainNotions.V.Lang.IsFinitePlace (Lp s.L) A ∧ ∀ v, Formalism.ConjugateSelfDual.IsPlaceOver (F := Lp s.L) A v → v ∉ S'

def Ip (u : s.St) : Subgroup s.GL_ := ((s.tau u).ker).map (Formalism.MainNotions.V.Lang.Ine (F := s.L) (s.Au u)).subtype

abbrev GLS : Type := Formalism.MainNotions.V.Lang.GS (F := s.L) TV.QbarQ
  {w | ∀ A : ValuationSubring TV.QbarQ, Formalism.ConjugateSelfDual.IsPlaceOver (F := s.L) A w →
    ∃ v, Formalism.ConjugateSelfDual.IsPlaceOver (F := Lp s.L) A v ∧ s.InS v}

structure TestRing (A : Type) [CommRing A] [IsLocalRing A] (j : s.O →+* A) : Prop where
  noeth : IsNoetherianRing A
  complete : IsAdicComplete (IsLocalRing.maximalIdeal A) A
  loc : IsLocalHom j
  res : Function.Surjective ((IsLocalRing.residue A).comp j)

def kTo {A : Type} [CommRing A] [IsLocalRing A] (j : s.O →+* A) (h : IsLocalHom j) :
    s.kk →+* IsLocalRing.ResidueField A := @IsLocalRing.ResidueField.map _ _ _ _ _ _ j h

def ContM {X : Type} [TopologicalSpace X] (A : Type) [CommRing A] [IsLocalRing A] (f : X → A) : Prop :=
  ∀ N : ℕ, @Continuous _ _ _ ⊥ (fun x => Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ N) (f x))

def oEl {A : Type} [CommRing A] (v : s.Vl) (ψ : Fin s.n → (s.Gv v →* Aˣ)) (g : Fin s.n → s.Gv v) :
    MonoidAlgebra A s.GL_ :=
  (List.ofFn fun i => MonoidAlgebra.single ((g i : s.GL_)) 1 -
    MonoidAlgebra.single 1 ((ψ i (g i) : Aˣ) : A)).prod

end HidaSetting

structure Resid (s : HidaSetting) where
  chib : Fin s.n → (s.GL_ →* s.kkˣ)
  chib_cont : ∀ i, @Continuous _ _ _ ⊥ (chib i)
  chib_unr : ∀ i (A : ValuationSubring TV.QbarQ), Formalism.MainNotions.V.Lang.IsFinitePlace (Lp s.L) A →
    (∀ v : HeightOneSpectrum (𝓞 (Lp s.L)), Formalism.ConjugateSelfDual.IsPlaceOver (F := Lp s.L) A v → ¬ s.InS v) →
    ∀ σ ∈ Formalism.MainNotions.V.Lang.Ine (F := s.L) A, chib i σ = 1
  chib_inj : Function.Injective chib

  Dstar : s.case = .U → ∀ (m : ℕ) (g : Fin m → s.GL_),
    Formalism.MainNotions.V.Lang.PsR.detPoly (fun i => ((s.omk (g i) ^ (1 - (s.n : ℤ)) : s.kkˣ) : s.kk) •
              HidaSetting.diagRep chib (s.conjL (g i))⁻¹) =
      Formalism.MainNotions.V.Lang.PsR.detPoly (fun i => HidaSetting.diagRep chib (g i))
  psib : ∀ v : s.Vl, Fin s.n → (s.Gv v →* s.kkˣ)
  psib_cont : ∀ v i, @Continuous _ _ _ ⊥ (psib v i)

structure Pair {s : HidaSetting} (r : Resid s) (art : s.ArtAt) (S' : Set (HeightOneSpectrum (𝓞 (Lp s.L))))
    (A : Type) [CommRing A] [IsLocalRing A] (j : s.O →+* A) (hj : IsLocalHom j)
    (D : Formalism.MainNotions.V.Lang.PsR.Det s.n A (MonoidAlgebra A s.GL_) A)
    (ψ : ∀ v : s.Vl, Fin s.n → (s.Gv v →* Aˣ)) : Prop where
  cont : ∀ (m : ℕ) (α : Fin m →₀ ℕ), HidaSetting.ContM A (fun g : Fin m → s.GL_ =>
    MvPolynomial.coeff α (D.D m (fun i => MonoidAlgebra.single (g i) 1)))
  lift : ∀ (m : ℕ) (g : Fin m → s.GL_),
    MvPolynomial.map (IsLocalRing.residue A) (D.D m (fun i => MonoidAlgebra.single (g i) 1)) =
      MvPolynomial.map (s.kTo j hj) (Formalism.MainNotions.V.Lang.PsR.detPoly (fun i => HidaSetting.diagRep r.chib (g i)))
  unr : ∀ A' : ValuationSubring TV.QbarQ, s.OutS S' A' → ∀ σ ∈ Formalism.MainNotions.V.Lang.Ine (F := s.L) A',
    D.Kills (MonoidAlgebra.single σ 1 - 1)
  psi_cont : ∀ v i, HidaSetting.ContM A (fun g : s.Gv v => ((ψ v i g : Aˣ) : A))
  psi_lift : ∀ v i g, IsLocalRing.residue A ((ψ v i g : Aˣ) : A) = s.kTo j hj ((r.psib v i g : s.kkˣ) : s.kk)
  psi_mu : s.case = .U → ∀ v i (ζ : (HeightOneSpectrum.adicCompletionIntegers s.L (s.vt v))ˣ), (∃ m : ℕ, ζ ^ (s.l ^ m) = 1) →
    Abelianization.lift (ψ v i) (art v (s.unitIncl v ζ)) = Units.map j.toMonoidHom (s.t0 (s.ej v i ζ))⁻¹

  psi_muD : s.case = .D → ∀ v i (ζ : (HeightOneSpectrum.adicCompletionIntegers s.L (s.vt v))ˣ), (∃ m : ℕ, ζ ^ (s.l ^ m) = 1) →
    Abelianization.lift (ψ v i) (art v (s.unitIncl v ζ)) = Units.map j.toMonoidHom ((s.t0 (s.ej v i ζ))⁻¹ *
      (if (i : ℕ) = 1 then Abelianization.lift (s.nuG.comp (s.Gv v).subtype) (art v (s.unitIncl v ζ)) else 1))

  P : s.case = .U → ∀ (g : s.GL_) (i : ℕ), D.lam i (s.starEl j (MonoidAlgebra.single g 1)) = D.lam i (MonoidAlgebra.single g 1)

  detD : s.case = .D → ∀ g : s.GL_, D.val (MonoidAlgebra.single g 1) = j (((s.epsO g)⁻¹ * s.nuG g : s.Oˣ) : s.O)

  O : ∀ (v : s.Vl) (g : Fin s.n → s.Gv v) (h : s.GL_),
    D.tr (MonoidAlgebra.single h 1 * s.oEl v (ψ v) g) = 0

  I : ∀ (u : s.St) (g : s.GL_), g ∈ s.Ip u → ∀ h : s.GL_,
    D.tr (MonoidAlgebra.single h 1 * (MonoidAlgebra.single g 1 - 1)) = 0

structure UniversalOrdinaryDeterminantRing {s : HidaSetting} (r : Resid s) (art : s.ArtAt) (S' : Set (HeightOneSpectrum (𝓞 (Lp s.L)))) where
  B : Type
  [instB : CommRing B]
  [instBL : IsLocalRing B]
  jB : s.O →+* B
  test : s.TestRing B jB
  D : Formalism.MainNotions.V.Lang.PsR.Det s.n B (MonoidAlgebra B s.GL_) B
  ψ : ∀ v : s.Vl, Fin s.n → (s.Gv v →* Bˣ)
  ok : Pair r art S' B jB test.loc D ψ
  univ : ∀ (A : Type) [CommRing A] [IsLocalRing A] (j : s.O →+* A) (hA : s.TestRing A j)
    (D' : Formalism.MainNotions.V.Lang.PsR.Det s.n A (MonoidAlgebra A s.GL_) A) (ψ' : ∀ v : s.Vl, Fin s.n → (s.Gv v →* Aˣ)),
    Pair r art S' A j hA.loc D' ψ' →
    ∃! φ : B →+* A, IsLocalHom φ ∧ φ.comp jB = j ∧ D.IsMap D' φ ∧
      ∀ v i g, Units.map φ.toMonoidHom (ψ v i g) = ψ' v i g

attribute [instance] UniversalOrdinaryDeterminantRing.instB UniversalOrdinaryDeterminantRing.instBL

namespace HidaSetting

variable (s : HidaSetting)

def Emb (v : s.Vl) : Type :=
  {τ : HeightOneSpectrum.adicCompletion s.L (s.vt v) →+* TV.QbarL s.l // Continuous τ}

def diagOf (t : s.TT) : ∀ v : s.Vl, Fin s.n → (HeightOneSpectrum.adicCompletionIntegers s.L (s.vt v))ˣ :=
  if h : s.case = .U then Function.surjInv (s.ttU h).2 t
  else if h' : s.case = .D then fun v j => if (j : ℕ) = 0 then Function.surjInv (s.ttD h').2 t v else 1
  else fun _ _ => 1

abbrev Weight : Type := ∀ v : s.Vl, s.Emb v → Fin s.n → ℤ

def IsDominant (lw : s.Weight) : Prop := ∀ v τ (i j : Fin s.n), i ≤ j → lw v τ j ≤ lw v τ i

def wtChar (lw : s.Weight) (t : s.TT) : (TV.QbarL s.l)ˣ :=
  ∏ᶠ (v : s.Vl), ∏ᶠ (τ : s.Emb v), ∏ j : Fin s.n,
    (Units.map (τ.1.toMonoidHom.comp (HeightOneSpectrum.adicCompletionIntegers s.L (s.vt v)).subtype.toMonoidHom)
      (s.diagOf t v j)) ^ (lw v τ j.rev)

def IsArithOf (lw : s.Weight) (θ : s.TT → (TV.QbarL s.l)ˣ) : Prop :=
  s.IsDominant lw ∧ ∃ (φ : s.TT →* (TV.QbarL s.l)ˣ) (c : ℕ), 1 ≤ c ∧ (∀ t ∈ s.fil c, φ t = 1) ∧
    (∀ t, θ t = φ t * s.wtChar lw t) ∧
    ∀ t, IsOfFinOrder t → (θ t : TV.QbarL s.l) = algebraMap s.O (TV.QbarL s.l) (s.t0 t : s.O)

def IsArith (θ : s.TT → (TV.QbarL s.l)ˣ) : Prop := ∃ lw, s.IsArithOf lw θ

def IsGood (θ : s.TT → (TV.QbarL s.l)ˣ) : Prop :=
  ∃ (lw : s.Weight) (φ : s.TT →* (TV.QbarL s.l)ˣ) (c : ℕ), s.IsDominant lw ∧ 1 ≤ c ∧
    (∀ t ∈ s.fil c, φ t = 1) ∧ (∀ t, θ t = φ t * s.wtChar lw t) ∧
    (∀ t, IsOfFinOrder t → (θ t : TV.QbarL s.l) = algebraMap s.O (TV.QbarL s.l) (s.t0 t : s.O)) ∧
    (∀ (v : s.Vl) (i j : Fin s.n), i ≠ j → φ.comp (s.ej v i) ≠ φ.comp (s.ej v j)) ∧
    (s.case = .D → ∀ v τ (h1 : 1 < s.n), lw v τ ⟨0, s.n_pos⟩ > lw v τ ⟨1, h1⟩ ∧
      lw v τ ⟨0, s.n_pos⟩ + lw v τ ⟨1, h1⟩ = -s.mD)

end HidaSetting

namespace Sys

variable {s : HidaSetting} (H : Sys s)

def OverTheta (mm : Ideal H.Tbig) [mm.IsMaximal] (x : H.T mm →+* TV.QbarL s.l)
    (θ : s.TT → (TV.QbarL s.l)ˣ) : Prop :=
  x.comp (H.oT mm) = algebraMap s.O (TV.QbarL s.l) ∧ ∀ t, x (H.brkT mm t) = θ t

end Sys

inductive LevelKind
  |   GL
  |   Iw
  |   Iw1
  deriving DecidableEq

structure TWData (s : HidaSetting) where
  Q : Finset (HeightOneSpectrum (𝓞 (Lp s.L)))
  Q_out : ∀ q ∈ Q, ¬ s.InS q
  qt : Q → HeightOneSpectrum (𝓞 s.L)

  Q_split : s.case = .U → ∀ q : Q, ∀ A : ValuationSubring TV.QbarQ, Formalism.ConjugateSelfDual.IsPlaceOver (F := Lp s.L) A q.1 →
    Formalism.MainNotions.V.Lang.Dec (F := Lp s.L) A ≤ (resPL s.L).range

  qt_over : ∀ q : Q, ∃ A : ValuationSubring TV.QbarQ, Formalism.ConjugateSelfDual.IsPlaceOver (F := Lp s.L) A q.1 ∧
    Formalism.ConjugateSelfDual.IsPlaceOver (F := s.L) A (qt q)
  lev : Q → LevelKind

abbrev TWData.Del {s : HidaSetting} (Q : TWData s) : Type :=
  ∀ q : {q : Q.Q // Q.lev q = .Iw1}, Fin s.n →
    ↥(CommGroup.primaryComponent ((𝓞 s.L ⧸ (Q.qt q.1).asIdeal)ˣ) s.l)

structure TWMod {s : HidaSetting} (H : Sys s) (mm : Ideal H.Tbig) [mm.IsMaximal] (Q : TWData s) where
  Mlev : Type
  [instM : AddCommGroup Mlev]
  [instMD : Module (MonoidAlgebra s.abelian₂ Q.Del) Mlev]
  Tp : Type
  [instTp : CommRing Tp]
  [instTpL : Algebra s.abelian₂ Tp]
  actp : Tp →+* Module.End (MonoidAlgebra s.abelian₂ Q.Del) Mlev
  actp_inj : Function.Injective actp

  psi : ∀ v : s.Vl, Fin s.n → (s.Gv v →* Tpˣ)

attribute [instance] TWMod.instM TWMod.instMD TWMod.instTp TWMod.instTpL

end VH

namespace VH

open IsDedekindDomain

def Iwc (s : HidaSetting) (c : ℕ) :
    Subgroup (∀ v : s.Vl, GL (Fin s.n) (HeightOneSpectrum.adicCompletionIntegers s.L (s.vt v))) :=
  Subgroup.closure {g | ∀ v (i j : Fin s.n), j < i →
    ((g v : GL (Fin s.n) _) : Matrix (Fin s.n) (Fin s.n) _) i j ∈
      IsLocalRing.maximalIdeal (HeightOneSpectrum.adicCompletionIntegers s.L (s.vt v)) ^ c}

def IwcLe (s : HidaSetting) (c : ℕ) : Iwc s (c + 1) →* Iwc s c :=
  Subgroup.inclusion (Subgroup.closure_mono (fun _ hg v i j hij =>
    Ideal.pow_le_pow_right (Nat.le_succ c) (hg v i j hij)))

end VH

namespace VH

@[reducible] def setLev {s : HidaSetting} (Q : TWData s) (lev' : Q.Q → LevelKind) : TWData s :=
  { Q with lev := lev' }

end VH

namespace VH

open IsDedekindDomain

def Tplus (s : HidaSetting) : Submonoid (∀ v : s.Vl, Fin s.n → (HeightOneSpectrum.adicCompletion s.L (s.vt v))ˣ) where
  carrier := {t | ∀ v (i j : Fin s.n), i ≤ j →
    Valued.v ((t v i : (HeightOneSpectrum.adicCompletion s.L (s.vt v))ˣ) : HeightOneSpectrum.adicCompletion s.L (s.vt v)) ≤
      Valued.v ((t v j : (HeightOneSpectrum.adicCompletion s.L (s.vt v))ˣ) : HeightOneSpectrum.adicCompletion s.L (s.vt v))}
  one_mem' := fun v i j _ => le_refl _
  mul_mem' := fun {a b} ha hb v i j h => by
    simp only [Pi.mul_apply, Units.val_mul, map_mul]
    exact mul_le_mul' (ha v i j h) (hb v i j h)

end VH

instance TV.instFiniteGaloisCharacters (D : D7) : Finite (TV.Chi ⟨D.R, D.host⟩) :=
  Finite.of_injective (fun f : TV.Chi ⟨D.R, D.host⟩ => (f : TV.GalE ⟨D.R, D.host⟩ → Multiplicative (ZMod (4 * D.R.n))))
    DFunLike.coe_injective

noncomputable instance TV.instFintypeGaloisCharacters (D : D7) : Fintype (TV.Chi ⟨D.R, D.host⟩) := Fintype.ofFinite _

structure VDataX (D : TV.XV) where

  embE : D.host.E →ₐ[ℚ] TV.QbarQ

  embC : TV.QbarQ →+* ℂ
  embC_embE : ∀ x : D.host.E, embC (embE x) = D.host.φ₀ x

  resE : TV.GQ →* TV.GalE D
  resE_spec : ∀ (g : TV.GQ) (x : D.host.E), embE (resE g x) = g (embE x)

  cc : TV.GQ
  cc_spec : ∀ x : TV.QbarQ, embC (cc x) = (starRingEnd ℂ) (embC x)

  artG : (ZMod (TV.condV D))ˣ →* TV.GalE D
  artG_frob : ∀ (p : ℕ) (hc : Nat.Coprime p (TV.condV D)), p.Prime →
    ∀ (P : Ideal (𝓞 D.host.E)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})],
    IsArithFrobAt ℤ (artG (ZMod.unitOfCoprime p hc))⁻¹ P

  Ol : ∀ (l : ℕ) [Fact l.Prime], Type
  [instRing : ∀ (l : ℕ) [Fact l.Prime], CommRing (Ol l)]
  [instDomain : ∀ (l : ℕ) [Fact l.Prime], IsDomain (Ol l)]
  [instLocal : ∀ (l : ℕ) [Fact l.Prime], IsLocalRing (Ol l)]
  [instAlg : ∀ (l : ℕ) [Fact l.Prime], Algebra ℤ_[l] (Ol l)]
  [instFin : ∀ (l : ℕ) [Fact l.Prime], Module.Finite ℤ_[l] (Ol l)]

  Ol_unram : ∀ (l : ℕ) [Fact l.Prime],
    IsLocalRing.maximalIdeal (Ol l) = Ideal.span {((l : ℕ) : Ol l)}

  zetaO : ∀ (l : ℕ) [Fact l.Prime], Ol l
  zetaO_prim : ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → IsPrimitiveRoot (zetaO l) (4 * D.R.n)

  omTil : ∀ (l : ℕ) [Fact l.Prime], TV.GQ →* ℤ_[l]ˣ
  omTil_pow : ∀ (l : ℕ) [Fact l.Prime] (g : TV.GQ), omTil l g ^ (l - 1) = 1
  omTil_red : ∀ (l : ℕ) [Fact l.Prime] (g : TV.GQ),
    PadicInt.toZMod (omTil l g : ℤ_[l]) = PadicInt.toZMod (TV.eps l g : ℤ_[l])

  iotaL : ∀ (l : ℕ) [Fact l.Prime], TV.QbarQ →+* TV.QbarL l

  iotaC : ∀ (l : ℕ) [Fact l.Prime], TV.QbarL l ≃+* ℂ
  iotaC_comp : ∀ (l : ℕ) [Fact l.Prime] (x : TV.QbarQ), iotaC l (iotaL l x) = embC x

  jO : ∀ (l : ℕ) [Fact l.Prime], Ol l →+* TV.QbarL l
  jO_inj : ∀ (l : ℕ) [Fact l.Prime], Function.Injective (jO l)
  jO_zp : ∀ (l : ℕ) [Fact l.Prime] (x : ℤ_[l]),
    jO l (algebraMap ℤ_[l] (Ol l) x) = algebraMap ℚ_[l] (TV.QbarL l) (x : ℚ_[l])

  zetaO_iota : ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 →
    iotaC l (jO l (zetaO l)) = ((TV.muC D (Multiplicative.ofAdd 1) : ℂˣ) : ℂ)

  plc : ℕ → ValuationSubring TV.QbarQ
  plc_above : ∀ q : ℕ, q.Prime → Formalism.MainNotions.V.Lang.IsPlaceAbove ℚ (plc q) q
  plc_l : ∀ (l : ℕ) [Fact l.Prime] (x : TV.QbarQ), x ∈ plc l ↔ ‖iotaL l x‖ ≤ 1

  spec : Formalism.ConjugateSelfDual.SpectrumFamily

  S3 : ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : TV.Chi D) (K : IntermediateField ℚ TV.QbarQ) (g1 : TV.GQ), Type
  [instUnitaryDeformationRing : ∀ (l : ℕ) [Fact l.Prime] e χ K g1, CommRing (S3 l e χ K g1)]
  [instS3alg : ∀ (l : ℕ) [Fact l.Prime] e χ K g1, Algebra (Ol l) (S3 l e χ K g1)]

  S3gr : ∀ (l : ℕ) [Fact l.Prime] e χ K g1, ℤ → Submodule (Ol l) (S3 l e χ K g1)
  [instS3gr : ∀ (l : ℕ) [Fact l.Prime] e χ K g1, GradedAlgebra (S3gr l e χ K g1)]

  unitaryGaloisRepresentation : ∀ (l : ℕ) [Fact l.Prime] e χ K g1, K.fixingSubgroup →* GL (Fin 3) (S3 l e χ K g1)

  unitary_rep_weights : ∀ (l : ℕ) [Fact l.Prime] e χ K g1 (g : K.fixingSubgroup) (i j : Fin 3),
    ((unitaryGaloisRepresentation l e χ K g1 g : GL (Fin 3) (S3 l e χ K g1)) : Matrix (Fin 3) (Fin 3) (S3 l e χ K g1)) i j ∈
      S3gr l e χ K g1 ((j : ℤ) - (i : ℤ))

  unitary_rep_dual : ∀ (l : ℕ) [Fact l.Prime] e χ K g1 (g h : K.fixingSubgroup), (h : TV.GQ) = cc * (g : TV.GQ)⁻¹ * cc →
    ((unitaryGaloisRepresentation l e χ K g1 h : GL (Fin 3) (S3 l e χ K g1)) : Matrix (Fin 3) (Fin 3) (S3 l e χ K g1)) =
      TV.Jad3 (S3 l e χ K g1) * ((unitaryGaloisRepresentation l e χ K g1 g : GL (Fin 3) (S3 l e χ K g1)) :
        Matrix (Fin 3) (Fin 3) (S3 l e χ K g1))ᵀ * TV.Jad3 (S3 l e χ K g1)

  unitary_rep_norm : ∀ (l : ℕ) [Fact l.Prime] e χ K g1,
    TV.IsNormalizedUnitaryLift K (TV.normEquationsThree (Ol l) g1 cc) (S3 l e χ K g1) (unitaryGaloisRepresentation l e χ K g1)

  pt3 : ∀ (l : ℕ) [Fact l.Prime] e χ K g1, l ≠ 2 → S3 l e χ K g1 →ₐ[Ol l] Ol l
  unitary_point_spec : ∀ (l : ℕ) [Fact l.Prime] e χ K g1 (hl : l ≠ 2) (g : K.fixingSubgroup),
    ((unitaryGaloisRepresentation l e χ K g1 g : GL (Fin 3) (S3 l e χ K g1)) : Matrix (Fin 3) (Fin 3) (S3 l e χ K g1)).map
        (pt3 l e χ K g1 hl) =
      Matrix.diagonal ![TV.psiRaw (Ol l) (zetaO l) resE l e χ g, 1, TV.psiRaw (Ol l) (zetaO l) resE l e χ (g⁻¹ : TV.GQ)]

  symplecticHeckeAlgebra : ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : TV.Chi D) (n' : ℕ) (ξ' : DirichletCharacter ℂ (2 ^ n')), Type
  [instSS4 : ∀ (l : ℕ) [Fact l.Prime] e χ n' ξ', CommRing (symplecticHeckeAlgebra l e χ n' ξ')]
  [instSS4alg : ∀ (l : ℕ) [Fact l.Prime] e χ n' ξ', Algebra (Ol l) (symplecticHeckeAlgebra l e χ n' ξ')]

  SS4gr : ∀ (l : ℕ) [Fact l.Prime] e χ n' ξ', (Fin 2 → ℤ) → Submodule (Ol l) (symplecticHeckeAlgebra l e χ n' ξ')
  [instSS4gr : ∀ (l : ℕ) [Fact l.Prime] e χ n' ξ', GradedAlgebra (SS4gr l e χ n' ξ')]

  symplecticGaloisRepresentation : ∀ (l : ℕ) [Fact l.Prime] e χ n' ξ', TV.GQ →* GL (Fin 4) (symplecticHeckeAlgebra l e χ n' ξ')

  symplecticHeckeCharacter : ∀ (l : ℕ) [Fact l.Prime] e χ n' ξ', TV.GQ →* (symplecticHeckeAlgebra l e χ n' ξ')ˣ
  symplectic_rep_similitude : ∀ (l : ℕ) [Fact l.Prime] e χ n' ξ' (g : TV.GQ),
    ((symplecticGaloisRepresentation l e χ n' ξ' g : GL (Fin 4) (symplecticHeckeAlgebra l e χ n' ξ')) : Matrix (Fin 4) (Fin 4) (symplecticHeckeAlgebra l e χ n' ξ'))ᵀ *
        TV.Jsp4 (symplecticHeckeAlgebra l e χ n' ξ') *
        ((symplecticGaloisRepresentation l e χ n' ξ' g : GL (Fin 4) (symplecticHeckeAlgebra l e χ n' ξ')) : Matrix (Fin 4) (Fin 4) (symplecticHeckeAlgebra l e χ n' ξ')) =
      ((symplecticHeckeCharacter l e χ n' ξ' g : (symplecticHeckeAlgebra l e χ n' ξ')ˣ) : symplecticHeckeAlgebra l e χ n' ξ') • TV.Jsp4 (symplecticHeckeAlgebra l e χ n' ξ')

  symplectic_rep_weights : ∀ (l : ℕ) [Fact l.Prime] e χ n' ξ' (g : TV.GQ) (i j : Fin 4),
    ((symplecticGaloisRepresentation l e χ n' ξ' g : GL (Fin 4) (symplecticHeckeAlgebra l e χ n' ξ')) : Matrix (Fin 4) (Fin 4) (symplecticHeckeAlgebra l e χ n' ξ')) i j ∈
      SS4gr l e χ n' ξ' (TV.wt4 i - TV.wt4 j)

  PCrys : ∀ (l : ℕ) [Fact l.Prime] (n : ℕ) (H : Subgroup TV.GQ) (A : ValuationSubring TV.QbarQ),
    (H →* GL (Fin n) (TV.QbarL l)) → Prop

  Crys : ∀ (l : ℕ) [Fact l.Prime] (n : ℕ) (H : Subgroup TV.GQ) (A : ValuationSubring TV.QbarQ),
    (H →* GL (Fin n) (TV.QbarL l)) → Prop

  DeRham : ∀ (l : ℕ) [Fact l.Prime] (n : ℕ) (H : Subgroup TV.GQ) (A : ValuationSubring TV.QbarQ),
    (H →* GL (Fin n) (TV.QbarL l)) → Prop

  HT : ∀ (l : ℕ) [Fact l.Prime] (n : ℕ) (H : Subgroup TV.GQ) (A : ValuationSubring TV.QbarQ),
    (H →* GL (Fin n) (TV.QbarL l)) → (IntermediateField.fixedField H →+* TV.QbarL l) → Multiset ℤ

  finiteCohomology : ∀ (l : ℕ) [Fact l.Prime] (n : ℕ) (H : Subgroup TV.GQ), (H →* GL (Fin n) (TV.QbarL l)) → Type
  [instAddCommGroupSelmer : ∀ (l : ℕ) [Fact l.Prime] n H ρ, AddCommGroup (finiteCohomology l n H ρ)]
  [instModuleSelmer : ∀ (l : ℕ) [Fact l.Prime] n H ρ, Module (TV.QbarL l) (finiteCohomology l n H ρ)]

  IsRA : ∀ (F : Type) [Field F] [NumberField F] (n : ℕ), (spec F n).Rep → Prop

  bkf : ∀ (l : ℕ) [Fact l.Prime] (n : ℕ) (ρ : TV.GQ →* GL (Fin n) (TV.QbarL l)),
    Submodule (TV.QbarL l) (TV.GQ → (Fin n → TV.QbarL l))

  bkg : ∀ (l : ℕ) [Fact l.Prime] (n : ℕ) (ρ : TV.GQ →* GL (Fin n) (TV.QbarL l)),
    Submodule (TV.QbarL l) (TV.GQ → (Fin n → TV.QbarL l))
  bkf_le : ∀ (l : ℕ) [Fact l.Prime] n ρ, bkf l n ρ ≤ TV.Z1 ρ

  bkf_conj : ∀ (l : ℕ) [Fact l.Prime] n ρ (M : GL (Fin n) (TV.QbarL l)) c,
    c ∈ bkf l n ρ ↔ (fun σ => (M : Matrix (Fin n) (Fin n) (TV.QbarL l)).mulVec (c σ)) ∈ bkf l n (TV.conjGL M ρ)

  selmer_eq : ∀ (l : ℕ) [Fact l.Prime] n (ρ : TV.GQ →* GL (Fin n) (TV.QbarL l)),
    Nonempty (finiteCohomology l n ⊤ (ρ.comp (⊤ : Subgroup TV.GQ).subtype) ≃ₗ[TV.QbarL l]
      (TV.SelP plc l ρ (bkf l n ρ) ⧸ (TV.B1 ρ).comap (TV.SelP plc l ρ (bkf l n ρ)).subtype))

  IsRA_all : ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (π : (spec F n).Rep), IsRA F n π

  S3hat : ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : TV.Chi D) (K : IntermediateField ℚ TV.QbarQ) (g1 : TV.GQ), Type
  [instS3hat : ∀ (l : ℕ) [Fact l.Prime] e χ K g1, CommRing (S3hat l e χ K g1)]
  [instS3hatL : ∀ (l : ℕ) [Fact l.Prime] e χ K g1, IsLocalRing (S3hat l e χ K g1)]
  [instS3hatA : ∀ (l : ℕ) [Fact l.Prime] e χ K g1, Algebra (Ol l) (S3hat l e χ K g1)]

  rS3hat : ∀ (l : ℕ) [Fact l.Prime] e χ K g1, K.fixingSubgroup →* GL (Fin 3) (S3hat l e χ K g1)

  unitary_ring_universal : ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : TV.Chi D) (K : IntermediateField ℚ TV.QbarQ) (g1 : TV.GQ), l ≠ 2 → Module.finrank ℚ K = 2 → cc ∉ K.fixingSubgroup →
    TV.IsUnivLiftN (Ol l) 3 K.fixingSubgroup
      (fun i g => ![TV.psiRaw (Ol l) (zetaO l) resE l e χ g, 1, TV.psiRaw (Ol l) (zetaO l) resE l e χ g⁻¹] i)
      (fun A _ _ _ s =>
        TV.IsLift3 (Ol l) K cc
          (fun i g => ![TV.psiRaw (Ol l) (zetaO l) resE l e χ g, 1, TV.psiRaw (Ol l) (zetaO l) resE l e χ g⁻¹] i) A s ∧
        TV.Cond3Raw (TV.condV D) plc l cc 1 1 K (Ol l) (jO l) (TV.normEquationsThree (Ol l) g1 cc)
          (fun i g => ![TV.psiRaw (Ol l) (zetaO l) resE l e χ g, 1, TV.psiRaw (Ol l) (zetaO l) resE l e χ g⁻¹] i)
          (TV.Ord3Raw (jO l)
            (fun i g => ![TV.psiRaw (Ol l) (zetaO l) resE l e χ g, 1, TV.psiRaw (Ol l) (zetaO l) resE l e χ g⁻¹] i)
            (Formalism.MainNotions.V.Lang.Dec (F := ℚ) (plc l)) (Formalism.MainNotions.V.Lang.Ine (F := ℚ) (plc l)) K.fixingSubgroup)
          A s)
      (S3hat l e χ K g1) (rS3hat l e χ K g1)

  S3emb : ∀ (l : ℕ) [Fact l.Prime] e χ K g1, S3 l e χ K g1 →+* S3hat l e χ K g1
  S3emb_O : ∀ (l : ℕ) [Fact l.Prime] e χ K g1,
    (S3emb l e χ K g1).comp (algebraMap (Ol l) (S3 l e χ K g1)) = algebraMap (Ol l) (S3hat l e χ K g1)
  S3emb_inj : ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : TV.Chi D) (K : IntermediateField ℚ TV.QbarQ) (g1 : TV.GQ), l ≠ 2 → Module.finrank ℚ K = 2 → cc ∉ K.fixingSubgroup → Function.Injective (S3emb l e χ K g1)
  S3emb_r : ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : TV.Chi D) (K : IntermediateField ℚ TV.QbarQ) (g1 : TV.GQ), l ≠ 2 → Module.finrank ℚ K = 2 → cc ∉ K.fixingSubgroup → ∀ g : K.fixingSubgroup,
    ((unitaryGaloisRepresentation l e χ K g1 g : GL (Fin 3) (S3 l e χ K g1)) : Matrix (Fin 3) (Fin 3) (S3 l e χ K g1)).map
      (S3emb l e χ K g1) = rS3hat l e χ K g1 g

  S3emb_wt : ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : TV.Chi D) (K : IntermediateField ℚ TV.QbarQ) (g1 : TV.GQ), l ≠ 2 → Module.finrank ℚ K = 2 → cc ∉ K.fixingSubgroup → ∀ (j : ℤ) (y : S3hat l e χ K g1),
    (∃ x ∈ S3gr l e χ K g1 j, S3emb l e χ K g1 x = y) ↔ TV.IsWt3 (Ol l) (rS3hat l e χ K g1) j y

  O4 : ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : TV.Chi D) (n' : ℕ) (ξ' : DirichletCharacter ℂ (2 ^ n')), Type
  [instCommRingSymplecticCoefficients : ∀ (l : ℕ) [Fact l.Prime] e χ n' ξ', CommRing (O4 l e χ n' ξ')]
  [instDomainSymplecticCoefficients : ∀ (l : ℕ) [Fact l.Prime] e χ n' ξ', IsDomain (O4 l e χ n' ξ')]
  [instLocalRingSymplecticCoefficients : ∀ (l : ℕ) [Fact l.Prime] e χ n' ξ', IsLocalRing (O4 l e χ n' ξ')]
  [instAlgebraSymplecticCoefficients : ∀ (l : ℕ) [Fact l.Prime] e χ n' ξ', Algebra (Ol l) (O4 l e χ n' ξ')]
  symplecticCoefficientEmbedding : ∀ (l : ℕ) [Fact l.Prime] e χ n' ξ', O4 l e χ n' ξ' →+* TV.QbarL l
  c4 : ∀ (l : ℕ) [Fact l.Prime] e χ n' ξ', Fin 4 → TV.GQ → O4 l e χ n' ξ'
  symplectic_coefficient_field : ∀ (l : ℕ) [Fact l.Prime] e χ n' ξ', l ≠ 2 →
    TV.IsCoef4Raw (Ol l) (jO l) (fun g => (TV.thLraw (iotaC l) resE (omTil l) e χ n' ξ' g : TV.QbarL l))
      (fun g => (TV.psiLraw (iotaC l) resE e χ g : TV.QbarL l))
      (fun g => (TV.alLraw (iotaC l) (omTil l) n' ξ' g : TV.QbarL l)) (O4 l e χ n' ξ') (symplecticCoefficientEmbedding l e χ n' ξ')
      (c4 l e χ n' ξ')

  symplectic_coefficients_unramified : ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : TV.Chi D) (n' : ℕ) (ξ' : DirichletCharacter ℂ (2 ^ n')), l ≠ 2 →
    IsLocalRing.maximalIdeal (O4 l e χ n' ξ') = Ideal.span {((l : ℕ) : O4 l e χ n' ξ')}

  symplecticPhase : ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : TV.Chi D) (n' : ℕ) (ξ' : DirichletCharacter ℂ (2 ^ n')), TV.GQ
  symplecticGaloisGenerator : ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : TV.Chi D) (n' : ℕ) (ξ' : DirichletCharacter ℂ (2 ^ n')), TV.GQ

  phg_spec : ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : TV.Chi D) (n' : ℕ) (ξ' : DirichletCharacter ℂ (2 ^ n')),
    l ≠ 2 → ¬ l ∣ TV.condV D →
    (∃ g, IsLocalRing.residue _ (c4 l e χ n' ξ' 1 g) ≠ 1) → (∃ g, IsLocalRing.residue _ (c4 l e χ n' ξ' 2 g) ≠ 1) →
    TV.IsNormDataRaw (plc l) l (c4 l e χ n' ξ') (symplecticPhase l e χ n' ξ') (symplecticGaloisGenerator l e χ n' ξ')

  SS4hat : ∀ (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : TV.Chi D) (n' : ℕ) (ξ' : DirichletCharacter ℂ (2 ^ n')), Type
  [instSS4hat : ∀ (l : ℕ) [Fact l.Prime] e χ n' ξ', CommRing (SS4hat l e χ n' ξ')]
  [instSS4hatL : ∀ (l : ℕ) [Fact l.Prime] e χ n' ξ', IsLocalRing (SS4hat l e χ n' ξ')]
  [instSS4hatA : ∀ (l : ℕ) [Fact l.Prime] e χ n' ξ', Algebra (O4 l e χ n' ξ') (SS4hat l e χ n' ξ')]
  rS4hat : ∀ (l : ℕ) [Fact l.Prime] e χ n' ξ', (⊤ : Subgroup TV.GQ) →* GL (Fin 4) (SS4hat l e χ n' ξ')

  symplectic_ring_universal : ∀ (l : ℕ) [Fact l.Prime] e χ n' ξ', l ≠ 2 → ¬ l ∣ TV.condV D →
    TV.IsUnivLift (O4 l e χ n' ξ') ⊤ (c4 l e χ n' ξ' 0) (c4 l e χ n' ξ')
      (fun A _ _ _ r => TV.SuchCondRaw D plc l (O4 l e χ n' ξ') (c4 l e χ n' ξ' 0) (c4 l e χ n' ξ') A r ∧
        TV.IsNorm4 (c4 l e χ n' ξ') (symplecticPhase l e χ n' ξ') (symplecticGaloisGenerator l e χ n' ξ') A r)
      (SS4hat l e χ n' ξ') (rS4hat l e χ n' ξ')

  SS4emb : ∀ (l : ℕ) [Fact l.Prime] e χ n' ξ', symplecticHeckeAlgebra l e χ n' ξ' →+* SS4hat l e χ n' ξ'
  SS4emb_O : ∀ (l : ℕ) [Fact l.Prime] e χ n' ξ',
    (SS4emb l e χ n' ξ').comp (algebraMap (Ol l) (symplecticHeckeAlgebra l e χ n' ξ')) =
      (algebraMap (O4 l e χ n' ξ') (SS4hat l e χ n' ξ')).comp (algebraMap (Ol l) (O4 l e χ n' ξ'))
  SS4emb_inj : ∀ (l : ℕ) [Fact l.Prime] e χ n' ξ', l ≠ 2 → ¬ l ∣ TV.condV D → Function.Injective (SS4emb l e χ n' ξ')
  SS4emb_r : ∀ (l : ℕ) [Fact l.Prime] e χ n' ξ', l ≠ 2 → ¬ l ∣ TV.condV D → ∀ g : TV.GQ,
    ((symplecticGaloisRepresentation l e χ n' ξ' g : GL (Fin 4) (symplecticHeckeAlgebra l e χ n' ξ')) : Matrix (Fin 4) (Fin 4) (symplecticHeckeAlgebra l e χ n' ξ')).map
      (SS4emb l e χ n' ξ') = rS4hat l e χ n' ξ' ⟨g, Subgroup.mem_top g⟩
  SS4emb_th : ∀ (l : ℕ) [Fact l.Prime] e χ n' ξ', l ≠ 2 → ¬ l ∣ TV.condV D → ∀ g : TV.GQ,
    SS4emb l e χ n' ξ' (symplecticHeckeCharacter l e χ n' ξ' g : symplecticHeckeAlgebra l e χ n' ξ') =
      algebraMap (O4 l e χ n' ξ') (SS4hat l e χ n' ξ') (c4 l e χ n' ξ' 0 g)

  SS4emb_wt : ∀ (l : ℕ) [Fact l.Prime] e χ n' ξ', l ≠ 2 → ¬ l ∣ TV.condV D → ∀ (j : Fin 2 → ℤ) (y : SS4hat l e χ n' ξ'),
    (∃ x ∈ SS4gr l e χ n' ξ' j, SS4emb l e χ n' ξ' x = y) ↔ TV.IsWt4 (O4 l e χ n' ξ') (rS4hat l e χ n' ξ') j y

structure VData (D : D7) extends VDataX ⟨D.R, D.host⟩ where

  shaE_len : ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ e : ℕ, 1 ≤ e → e < D.R.t →
    ∀ m : ℕ, Module.length ℤ_[l] (TV.ShaE embE l e) = m → D.what₂.shaLen l e = m

  pt4 : ∀ (l : ℕ) [Fact l.Prime] e χ n' ξ', l ≠ 2 → symplecticHeckeAlgebra l e χ n' ξ' →+* TV.QbarL l
  symplectic_point_coefficients : ∀ (l : ℕ) [Fact l.Prime] e χ n' ξ' (hl : l ≠ 2),
    (pt4 l e χ n' ξ' hl).comp (algebraMap (Ol l) (symplecticHeckeAlgebra l e χ n' ξ')) = jO l
  symplectic_point_spec : ∀ (l : ℕ) [Fact l.Prime] e χ n' ξ' (hl : l ≠ 2) (g : TV.GQ),
    ((symplecticGaloisRepresentation l e χ n' ξ' g : GL (Fin 4) (symplecticHeckeAlgebra l e χ n' ξ')) : Matrix (Fin 4) (Fin 4) (symplecticHeckeAlgebra l e χ n' ξ')).map
        (pt4 l e χ n' ξ' hl) =
      Matrix.diagonal ![(TV.thLraw (iotaC l) resE (omTil l) e χ n' ξ' g : TV.QbarL l),
        (TV.psiLraw (iotaC l) resE e χ g : TV.QbarL l), (TV.alLraw (iotaC l) (omTil l) n' ξ' g : TV.QbarL l), 1] ∧
    pt4 l e χ n' ξ' hl (symplecticHeckeCharacter l e χ n' ξ' g : symplecticHeckeAlgebra l e χ n' ξ') =
      (TV.thLraw (iotaC l) resE (omTil l) e χ n' ξ' g : TV.QbarL l)
  bkg_le : ∀ (l : ℕ) [Fact l.Prime] n ρ, bkg l n ρ ≤ TV.Z1 ρ

  bkf_loc : ∀ (l : ℕ) [Fact l.Prime] n ρ c, c ∈ TV.Z1 ρ → TV.CobOn ρ c (Formalism.MainNotions.V.Lang.Dec (F := ℚ) (plc l)) → c ∈ bkf l n ρ
  bkg_loc : ∀ (l : ℕ) [Fact l.Prime] n ρ c, c ∈ TV.Z1 ρ → TV.CobOn ρ c (Formalism.MainNotions.V.Lang.Dec (F := ℚ) (plc l)) → c ∈ bkg l n ρ
  bkg_conj : ∀ (l : ℕ) [Fact l.Prime] n ρ (M : GL (Fin n) (TV.QbarL l)) c,
    c ∈ bkg l n ρ ↔ (fun σ => (M : Matrix (Fin n) (Fin n) (TV.QbarL l)).mulVec (c σ)) ∈ bkg l n (TV.conjGL M ρ)

  fixW : ∀ (F : Type) [Field F] [NumberField F] (n : ℕ), (spec F n).Rep → IsDedekindDomain.HeightOneSpectrum (𝓞 F) → ℕ → Prop

  pure : ∀ (F : Type) [Field F] [NumberField F] (n : ℕ), (spec F n).Rep → Prop

  fullPS : ∀ (F : Type) [Field F] [NumberField F] (n : ℕ), (spec F n).Rep → IsDedekindDomain.HeightOneSpectrum (𝓞 F) → Prop

  wdSS : ∀ (l : ℕ) [Fact l.Prime] (F : Type) [Field F] [NumberField F] [Algebra F TV.QbarQ] (n : ℕ)
    (A : ValuationSubring TV.QbarQ), (Formalism.MainNotions.V.Lang.Dec (F := F) A →* GL (Fin n) (TV.QbarL l)) →
    (Fin n → (Formalism.MainNotions.V.Lang.Dec (F := F) A →* (TV.QbarL l)ˣ)) → Prop

  wdInChars : ∀ (l : ℕ) [Fact l.Prime] (F : Type) [Field F] [NumberField F] [Algebra F TV.QbarQ] (n : ℕ)
    (A : ValuationSubring TV.QbarQ), (Formalism.MainNotions.V.Lang.Dec (F := F) A →* GL (Fin n) (TV.QbarL l)) →
    (Fin n → (Formalism.MainNotions.V.Lang.Dec (F := F) A →* (TV.QbarL l)ˣ)) → Prop

  drChar : ∀ (l : ℕ) [Fact l.Prime] (F : Type) [Field F] [NumberField F] [Algebra F TV.QbarQ]
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (A : ValuationSubring TV.QbarQ),
    (Formalism.MainNotions.V.Lang.Dec (F := F) A →* (TV.QbarL l)ˣ) →
    ({τ : w.adicCompletion F →+* TV.QbarL l // Continuous τ} → ℤ) → Prop

  potCrys : ∀ (l : ℕ) [Fact l.Prime] (F : Type) [Field F] [NumberField F] [Algebra F TV.QbarQ] (n : ℕ)
    (A : ValuationSubring TV.QbarQ), (Formalism.MainNotions.V.Lang.Dec (F := F) A →* GL (Fin n) (TV.QbarL l)) → Prop

  crys : ∀ (l : ℕ) [Fact l.Prime] (F : Type) [Field F] [NumberField F] [Algebra F TV.QbarQ] (n : ℕ)
    (A : ValuationSubring TV.QbarQ), (Formalism.MainNotions.V.Lang.Dec (F := F) A →* GL (Fin n) (TV.QbarL l)) → Prop

  crys_pot : ∀ (l : ℕ) [Fact l.Prime] (F : Type) [Field F] [NumberField F] [Algebra F TV.QbarQ] (n : ℕ)
    (A : ValuationSubring TV.QbarQ) (ρ : Formalism.MainNotions.V.Lang.Dec (F := F) A →* GL (Fin n) (TV.QbarL l)),
    crys l F n A ρ → potCrys l F n A ρ

  ratioNot : ∀ (l : ℕ) [Fact l.Prime] (F : Type) [Field F] [NumberField F] [Algebra F TV.QbarQ]
    (A : ValuationSubring TV.QbarQ), (Formalism.MainNotions.V.Lang.Dec (F := F) A →* (TV.QbarL l)ˣ) →
    (Formalism.MainNotions.V.Lang.Dec (F := F) A →* (TV.QbarL l)ˣ) → Prop

  algChar : ∀ (l : ℕ) [Fact l.Prime] (F : Type) [Field F] [NumberField F] [Algebra F TV.QbarQ],
    (Formalism.ConjugateSelfDual.G F TV.QbarQ →* (TV.QbarL l)ˣ) → Prop

  artLoc : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω), Formalism.ConjugateSelfDual.IsPlaceOver (F := F) A v →
    (v.adicCompletion F)ˣ →* Abelianization (Formalism.MainNotions.V.Lang.Dec (F := F) A)

  artLoc_units : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (h : Formalism.ConjugateSelfDual.IsPlaceOver (F := F) A v),
    ((artLoc F Ω v A h).comp
        (Units.map (v.adicCompletionIntegers F).toSubring.subtype.toMonoidHom)).range =
      ((Formalism.MainNotions.V.Lang.Ine (F := F) A).subgroupOf (Formalism.MainNotions.V.Lang.Dec (F := F) A)).map
        Abelianization.of

  artLoc_unif : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (h : Formalism.ConjugateSelfDual.IsPlaceOver (F := F) A v)
    (ϖ : (v.adicCompletion F)ˣ), Valued.v (ϖ : v.adicCompletion F) < 1 →
    (∀ x : v.adicCompletion F, Valued.v x < 1 → Valued.v x ≤ Valued.v (ϖ : v.adicCompletion F)) →
    ∃ σ : Formalism.MainNotions.V.Lang.Dec (F := F) A, artLoc F Ω v A h ϖ = Abelianization.of σ ∧
      Formalism.ConjugateSelfDual.IsFrob (F := F) A (Formalism.ConjugateSelfDual.normV v) ((σ : Formalism.ConjugateSelfDual.G F Ω)⁻¹)

  DdR : ∀ (l : ℕ) [Fact l.Prime] (n : ℕ), (TV.GQ →* GL (Fin n) (TV.QbarL l)) → Type
  [instDdRa : ∀ (l : ℕ) [Fact l.Prime] n ρ, AddCommGroup (DdR l n ρ)]
  [instDdRm : ∀ (l : ℕ) [Fact l.Prime] n ρ, Module (TV.QbarL l) (DdR l n ρ)]

  expS : ∀ (l : ℕ) [Fact l.Prime] n ρ, (TV.GQ → (Fin n → TV.QbarL l)) →ₗ[TV.QbarL l] DdR l n ρ
  expS_loc : ∀ (l : ℕ) [Fact l.Prime] n ρ c, c ∈ TV.Z1 ρ → TV.CobOn ρ c (Formalism.MainNotions.V.Lang.Dec (F := ℚ) (plc l)) → expS l n ρ c = 0

  kato : ∀ (l : ℕ) [Fact l.Prime] (e N : ℕ) (χ : DirichletCharacter ℂ N)
    (f : CuspForm (CongruenceSubgroup.Gamma1 N) ((2 * e + 1 : ℕ) : ℤ)), TV.IsNewform f χ → Nat.Coprime N l →
    ∀ ι : TV.QbarL l →+* ℂ, TV.KatoSys plc l e f ι (DdR l) (expS l)

  hida : ∀ s : VH.HidaSetting, VH.Sys s

  hidaLoc : ∀ (s : VH.HidaSetting) (mm : Ideal (hida s).Tbig) [mm.IsMaximal],
    VH.Loc (hida s) mm (fun v => artLoc s.L TV.QbarQ (s.vt v) (s.At v) (s.At_over v))

  hidaTW : ∀ (s : VH.HidaSetting) (mm : Ideal (hida s).Tbig) [mm.IsMaximal] (Q : VH.TWData s),
    VH.TWMod (hida s) mm Q
  tauO : VH.HidaSetting → Type
  [instTauA : ∀ s, AddCommGroup (tauO s)]
  [instTauM : ∀ s : VH.HidaSetting, Module s.O (tauO s)]
  Sc : ∀ (s : VH.HidaSetting) (c : ℕ) (W : Type) [AddCommGroup W] [Module s.O W],
    (VH.Iwc s c →* (W →ₗ[s.O] W)) → Type
  [instScA : ∀ (s : VH.HidaSetting) c W [AddCommGroup W] [Module s.O W] act, AddCommGroup (@Sc s c W _ _ act)]
  [instScM : ∀ (s : VH.HidaSetting) c W [AddCommGroup W] [Module s.O W] act, Module s.O (@Sc s c W _ _ act)]
  incl : ∀ (s : VH.HidaSetting) (c : ℕ) (W : Type) [AddCommGroup W] [Module s.O W]
    (act : VH.Iwc s c →* (W →ₗ[s.O] W)), Sc s c W act →ₗ[s.O] Sc s (c + 1) W (act.comp (VH.IwcLe s c))

  isDel : ∀ (s : VH.HidaSetting) (c : ℕ) (W : Type) [AddCommGroup W] [Module s.O W],
    (VH.Iwc s c →* (W →ₗ[s.O] W)) → (VH.Tplus s →* (W →ₗ[s.O] W)) → Prop

  ordE : ∀ (s : VH.HidaSetting) (c : ℕ) (W : Type) [AddCommGroup W] [Module s.O W]
    (act : VH.Iwc s c →* (W →ₗ[s.O] W)) (tp : VH.Tplus s →* (W →ₗ[s.O] W)), Module.End s.O (Sc s c W act)
  Uz : ∀ (s : VH.HidaSetting) (c : ℕ) (W : Type) [AddCommGroup W] [Module s.O W]
    (act : VH.Iwc s c →* (W →ₗ[s.O] W)) (tp : VH.Tplus s →* (W →ₗ[s.O] W)), Module.End s.O (Sc s c W act)
  ordE_idem : ∀ (s : VH.HidaSetting) c W [AddCommGroup W] [Module s.O W] act tp,
    ordE s c W act tp * ordE s c W act tp = ordE s c W act tp
  ordE_comm : ∀ (s : VH.HidaSetting) c W [AddCommGroup W] [Module s.O W] act tp,
    ordE s c W act tp * Uz s c W act tp = Uz s c W act tp * ordE s c W act tp
  MlamPh : ∀ (s : VH.HidaSetting) (lw : s.Weight) (φ : s.TT →* (TV.QbarL s.l)ˣ) (c : ℕ) (R : Type)
    [CommRing R] [Algebra s.O R], Type
  [instMA : ∀ (s : VH.HidaSetting) lw φ c R [CommRing R] [Algebra s.O R], AddCommGroup (@MlamPh s lw φ c R _ _)]
  [instMM : ∀ (s : VH.HidaSetting) lw φ c R [CommRing R] [Algebra s.O R], Module s.O (@MlamPh s lw φ c R _ _)]
  MlamAct : ∀ (s : VH.HidaSetting) (lw : s.Weight) (φ : s.TT →* (TV.QbarL s.l)ˣ) (c : ℕ) (R : Type)
    [CommRing R] [Algebra s.O R], VH.Iwc s c →* (MlamPh s lw φ c R →ₗ[s.O] MlamPh s lw φ c R)

  MlamTp : ∀ (s : VH.HidaSetting) (lw : s.Weight) (φ : s.TT →* (TV.QbarL s.l)ˣ) (c : ℕ) (R : Type)
    [CommRing R] [Algebra s.O R], VH.Tplus s →* (MlamPh s lw φ c R →ₗ[s.O] MlamPh s lw φ c R)

  heckeS : ∀ (s : VH.HidaSetting) (lw : s.Weight) (φ : s.TT →* (TV.QbarL s.l)ˣ) (c : ℕ) (R : Type)
    [CommRing R] [Algebra s.O R], (hida s).Tbig →ₙ+* Module.End s.O
      (Sc s c (MlamPh s lw φ c R) (MlamAct s lw φ c R))
  kTh : ∀ s : VH.HidaSetting, VH.Iwc s 1 →* (s.kk →ₗ[s.O] s.kk)

  kThTp : ∀ s : VH.HidaSetting, VH.Tplus s →* (s.kk →ₗ[s.O] s.kk)
  toK : ∀ s : VH.HidaSetting, s.Lamf →+* s.kk
  toK_O : ∀ s : VH.HidaSetting, (toK s).comp (algebraMap s.O s.Lamf) = IsLocalRing.residue s.O
  SmRep : ∀ (s : VH.HidaSetting), s.Vl → Type
  nInd : ∀ (s : VH.HidaSetting) (v : s.Vl), SmRep s v →
    (Fin s.n → ((IsDedekindDomain.HeightOneSpectrum.adicCompletion s.L (s.vt v))ˣ →* ℂˣ)) → Prop
  indIrr : ∀ (s : VH.HidaSetting) (v : s.Vl),
    (Fin s.n → ((IsDedekindDomain.HeightOneSpectrum.adicCompletion s.L (s.vt v))ˣ →* ℂˣ)) → Prop
  ordVec : ∀ (s : VH.HidaSetting) (v : s.Vl), SmRep s v →
    (Fin s.n → ((IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers s.L (s.vt v))ˣ →* ℂˣ)) →
    (Fin s.n → ℂ) → Prop
  ordLine : ∀ (s : VH.HidaSetting) (v : s.Vl), SmRep s v →
    (Fin s.n → ((IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers s.L (s.vt v))ˣ →* ℂˣ)) → Prop
  wdRec : ∀ (s : VH.HidaSetting) (v : s.Vl), (s.Gv v →* GL (Fin s.n) (TV.QbarL s.l)) → SmRep s v → Prop
  psOf : ∀ (s : VH.HidaSetting) (v : s.Vl),
    (Fin s.n → ((IsDedekindDomain.HeightOneSpectrum.adicCompletion s.L (s.vt v))ˣ →* ℂˣ)) →
    s.Weight → Fin s.n → (s.Gv v →* (TV.QbarL s.l)ˣ)
  drRep : ∀ (s : VH.HidaSetting) (v : s.Vl), (s.Gv v →* GL (Fin s.n) (TV.QbarL s.l)) → (s.Emb v → Multiset ℤ) → Prop
  smulQ : ∀ (s : VH.HidaSetting) (lw : s.Weight) (φ : s.TT →* (TV.QbarL s.l)ˣ) (c : ℕ), TV.QbarL s.l →
    Module.End s.O (Sc s c (MlamPh s lw φ c (TV.QbarL s.l)) (MlamAct s lw φ c (TV.QbarL s.l)))
  WDty : Type
  sigmas : ∀ (s : VH.HidaSetting) (mm : Ideal (hida s).Tbig) [mm.IsMaximal] (Q : VH.TWData s),
    ((MonoidAlgebra s.abelian₂ Q.Del) →+* TV.QbarL s.l) → Type
  rSig : ∀ (s : VH.HidaSetting) (mm : Ideal (hida s).Tbig) [mm.IsMaximal] (Q : VH.TWData s) θh,
    sigmas s mm Q θh → (s.GL_ →* GL (Fin s.n) (TV.QbarL s.l))
  wdq : ∀ (s : VH.HidaSetting) (q : IsDedekindDomain.HeightOneSpectrum (𝓞 s.L)), (s.GL_ →* GL (Fin s.n) (TV.QbarL s.l)) → WDty

  recq : ∀ (s : VH.HidaSetting) (mm : Ideal (hida s).Tbig) [mm.IsMaximal] (Q : VH.TWData s) θh,
    sigmas s mm Q θh → IsDedekindDomain.HeightOneSpectrum (𝓞 s.L) → WDty

  Hq : ∀ (s : VH.HidaSetting) (Q : VH.TWData s), Q.Q → Type
  [instHq : ∀ (s : VH.HidaSetting) (Q : VH.TWData s) (q : Q.Q), Ring (Hq s Q q)]

  hq : ∀ (s : VH.HidaSetting) (mm : Ideal (hida s).Tbig) [mm.IsMaximal] (Q : VH.TWData s) (q : Q.Q),
    Hq s Q q →+* AddMonoid.End (hidaTW s mm Q).Mlev

  tq : ∀ (s : VH.HidaSetting) (Q : VH.TWData s) (q : Q.Q), Fin s.n →
    ((IsDedekindDomain.HeightOneSpectrum.adicCompletion s.L (Q.qt q))ˣ →* (Hq s Q q)ˣ)

  inc : ∀ (s : VH.HidaSetting) (mm : Ideal (hida s).Tbig) [mm.IsMaximal] (Q : VH.TWData s)
    (lev' : Q.Q → VH.LevelKind), (hidaTW s mm Q).Mlev →+ (hidaTW s mm (VH.setLev Q lev')).Mlev

  tr : ∀ (s : VH.HidaSetting) (mm : Ideal (hida s).Tbig) [mm.IsMaximal] (Q : VH.TWData s)
    (lev' : Q.Q → VH.LevelKind), (hidaTW s mm (VH.setLev Q lev')).Mlev →+ (hidaTW s mm Q).Mlev

  Msig : ∀ (s : VH.HidaSetting) (mm : Ideal (hida s).Tbig) [mm.IsMaximal] (Q : VH.TWData s)
    (θh : MonoidAlgebra s.abelian₂ Q.Del →+* TV.QbarL s.l), sigmas s mm Q θh → Type
  [instMsA : ∀ (s : VH.HidaSetting) (mm : Ideal (hida s).Tbig) [mm.IsMaximal] (Q : VH.TWData s)
    (θh : MonoidAlgebra s.abelian₂ Q.Del →+* TV.QbarL s.l) (σ : sigmas s mm Q θh), AddCommGroup (Msig s mm Q θh σ)]
  [instMsM : ∀ (s : VH.HidaSetting) (mm : Ideal (hida s).Tbig) [mm.IsMaximal] (Q : VH.TWData s)
    (θh : MonoidAlgebra s.abelian₂ Q.Del →+* TV.QbarL s.l) (σ : sigmas s mm Q θh),
    Module (TV.QbarL s.l) (Msig s mm Q θh σ)]

  pSig : ∀ (s : VH.HidaSetting) (mm : Ideal (hida s).Tbig) [mm.IsMaximal] (Q : VH.TWData s)
    (θh : MonoidAlgebra s.abelian₂ Q.Del →+* TV.QbarL s.l) (σ : sigmas s mm Q θh),
    (hidaTW s mm Q).Mlev →+ Msig s mm Q θh σ

  hSig : ∀ (s : VH.HidaSetting) (mm : Ideal (hida s).Tbig) [mm.IsMaximal] (Q : VH.TWData s)
    (θh : MonoidAlgebra s.abelian₂ Q.Del →+* TV.QbarL s.l) (σ : sigmas s mm Q θh) (q : Q.Q),
    Hq s Q q →+* Module.End (TV.QbarL s.l) (Msig s mm Q θh σ)

attribute [instance] VData.instHq VData.instMsA VData.instMsM
attribute [instance] VData.instTauA VData.instTauM VData.instScA VData.instScM VData.instMA VData.instMM
attribute [instance] VDataX.instRing VDataX.instDomain VDataX.instLocal VDataX.instAlg VDataX.instFin
  VDataX.instUnitaryDeformationRing VDataX.instS3alg VDataX.instS3gr
  VDataX.instSS4 VDataX.instSS4alg VDataX.instSS4gr VDataX.instAddCommGroupSelmer VDataX.instModuleSelmer VData.instDdRa VData.instDdRm

attribute [instance] VDataX.instS3hat VDataX.instS3hatL VDataX.instS3hatA VDataX.instCommRingSymplecticCoefficients VDataX.instDomainSymplecticCoefficients VDataX.instLocalRingSymplecticCoefficients
  VDataX.instAlgebraSymplecticCoefficients VDataX.instSS4hat VDataX.instSS4hatL VDataX.instSS4hatA

namespace VData

variable {D : D7} (V : VData D)

def artA : (ZMod (TV.condV D))ˣ →* TV.GalE D where
  toFun a := V.artG a⁻¹
  map_one' := by simp
  map_mul' a b := by rw [mul_inv, map_mul]

def bridge_art : Prop := ∀ a, V.artA a = (V.artG a)⁻¹

def chiDir (χ : TV.Chi D) : DirichletCharacter ℂ (TV.condV D) :=
  MulChar.ofUnitHom ((TV.chiC χ).comp V.artA)

def chiGQ (χ : TV.Chi D) : TV.GQ →* ℂˣ := (TV.chiC χ).comp V.resE

def chiO (l : ℕ) [Fact l.Prime] (χ : TV.Chi D) (σ : TV.GalE D) : V.Ol l :=
  V.zetaO l ^ (Multiplicative.toAdd (χ σ)).val

abbrev kl (l : ℕ) [Fact l.Prime] : Type := IsLocalRing.ResidueField (V.Ol l)

abbrev zO (l : ℕ) [Fact l.Prime] : ℤ_[l] →+* V.Ol l := algebraMap ℤ_[l] (V.Ol l)

def psi (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : TV.Chi D) (g : TV.GQ) : V.Ol l :=
  V.zO l (TV.eps l g : ℤ_[l]) ^ e * V.chiO l χ (V.resE g)

def omBar (l : ℕ) [Fact l.Prime] (g : TV.GQ) : V.kl l :=
  IsLocalRing.residue (V.Ol l) (V.zO l (TV.eps l g : ℤ_[l]))

def psiBar (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : TV.Chi D) (g : TV.GQ) : V.kl l :=
  IsLocalRing.residue (V.Ol l) (V.psi l e χ g)

def aOf (l : ℕ) (χ : TV.Chi D) : ℕ := if l ∣ (V.chiDir χ).conductor then (l - 1) / 2 else 0

def chiPr (l : ℕ) [Fact l.Prime] (χ : TV.Chi D) (g : TV.GQ) : V.Ol l :=
  V.zO l (((V.omTil l g)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) ^ V.aOf l χ * V.chiO l χ (V.resE g)

def PsiEven (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : TV.Chi D) : Prop := V.psi l e χ V.cc = 1

abbrev shaE (l : ℕ) [Fact l.Prime] (e : ℕ) : Type := TV.ShaE V.embE l e

abbrev shaO (l : ℕ) [Fact l.Prime] (e : ℕ) : Type := TensorProduct ℤ_[l] (V.Ol l) (V.shaE l e)

def wChi (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : TV.Chi D) (g : TV.GQ) : V.Ol l :=
  V.zO l (TV.epsNeg l e g) * V.chiO l χ (V.resE g⁻¹)

def shaChiConds (l : ℕ) (χ : TV.Chi D) : Set (Subgroup TV.GQ) :=
  {H' | ∃ A : ValuationSubring TV.QbarQ,
    (Formalism.MainNotions.V.Lang.IsPlaceAbove ℚ A l ∧ H' = Formalism.MainNotions.V.Lang.Dec (F := ℚ) A) ∨
      (Formalism.MainNotions.V.Lang.IsFinitePlace ℚ A ∧ ¬ Formalism.MainNotions.V.Lang.IsPlaceAbove ℚ A l ∧
        H' = Formalism.MainNotions.V.Lang.Ine (F := ℚ) A ⊓ (χ.comp V.resE).ker)}

abbrev shaChi (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : TV.Chi D) : Type :=
  TV.SelmerGroupAlt (V.Ol l) (TV.KO (V.Ol l)) ⊤ (V.wChi l e χ) (V.shaChiConds l χ)

def Vlen (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : TV.Chi D) : ℕ∞ := Module.length (V.Ol l) (V.shaChi l e χ)

def Vq (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : TV.Chi D) : ℚ := ((V.Vlen l e χ).toNat : ℚ)

def Dq (q : ℕ) : Subgroup TV.GQ := Formalism.MainNotions.V.Lang.Dec (F := ℚ) (V.plc q)

def Iq (q : ℕ) : Subgroup TV.GQ := Formalism.MainNotions.V.Lang.Ine (F := ℚ) (V.plc q)

abbrev GK (K : IntermediateField ℚ TV.QbarQ) : Subgroup TV.GQ := K.fixingSubgroup

def chiL (l : ℕ) [Fact l.Prime] (χ : TV.Chi D) : TV.GQ →* (TV.QbarL l)ˣ := TV.chiLraw (V.iotaC l) V.resE χ

def psiL (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : TV.Chi D) : TV.GQ →* (TV.QbarL l)ˣ := TV.psiLraw (V.iotaC l) V.resE e χ

def omTilL (l : ℕ) [Fact l.Prime] : TV.GQ →* (TV.QbarL l)ˣ := TV.toLZ (V.omTil l)

def xiL (l : ℕ) [Fact l.Prime] (n' : ℕ) (ξ' : DirichletCharacter ℂ (2 ^ n')) : TV.GQ →* (TV.QbarL l)ˣ :=
  TV.xiLraw (V.iotaC l) n' ξ'

def alL (l : ℕ) [Fact l.Prime] (n' : ℕ) (ξ' : DirichletCharacter ℂ (2 ^ n')) : TV.GQ →* (TV.QbarL l)ˣ :=
  TV.alLraw (V.iotaC l) (V.omTil l) n' ξ'

def thL (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : TV.Chi D) (n' : ℕ) (ξ' : DirichletCharacter ℂ (2 ^ n')) :
    TV.GQ →* (TV.QbarL l)ˣ := TV.thLraw (V.iotaC l) V.resE (V.omTil l) e χ n' ξ'

def beL (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : TV.Chi D) (n' : ℕ) (ξ' : DirichletCharacter ℂ (2 ^ n')) :
    TV.GQ →* (TV.QbarL l)ˣ := V.psiL l e χ * (V.alL l n' ξ')⁻¹

abbrev S3zero (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : TV.Chi D) (K : IntermediateField ℚ TV.QbarQ) (g1 : TV.GQ) :
    Submodule (V.Ol l) (V.S3 l e χ K g1) := V.S3gr l e χ K g1 0

def IsPt3 {l : ℕ} [Fact l.Prime] {e : ℕ} {χ : TV.Chi D} {K : IntermediateField ℚ TV.QbarQ} {g1 : TV.GQ}
    (ξ : V.S3 l e χ K g1 →+* TV.QbarL l) : Prop :=
  ξ.comp (algebraMap (V.Ol l) (V.S3 l e χ K g1)) = V.jO l

def rho3 {l : ℕ} [Fact l.Prime] {e : ℕ} {χ : TV.Chi D} {K : IntermediateField ℚ TV.QbarQ} {g1 : TV.GQ}
    (ξ : V.S3 l e χ K g1 →+* TV.QbarL l) : K.fixingSubgroup →* GL (Fin 3) (TV.QbarL l) :=
  (Units.map (ξ.mapMatrix : Matrix (Fin 3) (Fin 3) (V.S3 l e χ K g1) →+* Matrix (Fin 3) (Fin 3) (TV.QbarL l)).toMonoidHom).comp
    (V.unitaryGaloisRepresentation l e χ K g1)

abbrev SS4inv (l : ℕ) [Fact l.Prime] (e : ℕ) (χ : TV.Chi D) (n' : ℕ) (ξ' : DirichletCharacter ℂ (2 ^ n')) :
    Submodule (V.Ol l) (V.symplecticHeckeAlgebra l e χ n' ξ') := V.SS4gr l e χ n' ξ' 0

def IsPt4 {l : ℕ} [Fact l.Prime] {e : ℕ} {χ : TV.Chi D} {n' : ℕ} {ξ' : DirichletCharacter ℂ (2 ^ n')}
    (ξ : V.symplecticHeckeAlgebra l e χ n' ξ' →+* TV.QbarL l) : Prop :=
  ξ.comp (algebraMap (V.Ol l) (V.symplecticHeckeAlgebra l e χ n' ξ')) = V.jO l ∧
    (∀ g : TV.GQ, ξ (V.symplecticHeckeCharacter l e χ n' ξ' g : V.symplecticHeckeAlgebra l e χ n' ξ') = (V.thL l e χ n' ξ' g : TV.QbarL l)) ∧
    ∀ (a : V.O4 l e χ n' ξ') (x : V.symplecticHeckeAlgebra l e χ n' ξ'),
      V.SS4emb l e χ n' ξ' x = algebraMap (V.O4 l e χ n' ξ') (V.SS4hat l e χ n' ξ') a → ξ x = V.symplecticCoefficientEmbedding l e χ n' ξ' a

def rho4 {l : ℕ} [Fact l.Prime] {e : ℕ} {χ : TV.Chi D} {n' : ℕ} {ξ' : DirichletCharacter ℂ (2 ^ n')}
    (ξ : V.symplecticHeckeAlgebra l e χ n' ξ' →+* TV.QbarL l) : TV.GQ →* GL (Fin 4) (TV.QbarL l) :=
  (Units.map (ξ.mapMatrix : Matrix (Fin 4) (Fin 4) (V.symplecticHeckeAlgebra l e χ n' ξ') →+* Matrix (Fin 4) (Fin 4) (TV.QbarL l)).toMonoidHom).comp
    (V.symplecticGaloisRepresentation l e χ n' ξ')

def toRecRep {K : IntermediateField ℚ TV.QbarQ} {R : Type} [Group R] (ρ : K.fixingSubgroup →* R) :
    Formalism.ConjugateSelfDual.G K TV.QbarQ →* R :=
  ρ.comp (IntermediateField.fixingSubgroupEquiv K).symm.toMonoidHom

def Vchi (l e : ℕ) (χ : TV.Chi D) : ℚ :=
  if h : l.Prime then haveI : Fact l.Prime := ⟨h⟩; V.Vq l e χ else 0

end VData

namespace TV

open Formalism.ConjugateSelfDual Filter Polynomial IsDedekindDomain

def conjV {L : Type} [Field L] [NumberField L] (s : L ≃+* L) (w : HeightOneSpectrum (𝓞 L)) :
    HeightOneSpectrum (𝓞 L) where
  asIdeal := w.asIdeal.comap (RingOfIntegers.mapRingEquiv s.symm : 𝓞 L →+* 𝓞 L)
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := by
    obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot w.ne_bot
    refine (Submodule.ne_bot_iff _).mpr ⟨RingOfIntegers.mapRingEquiv s y, ?_, ?_⟩
    · rw [Ideal.mem_comap]
      convert hy using 1
      exact RingOfIntegers.ext (by simp)
    · exact (map_ne_zero_iff _ (RingOfIntegers.mapRingEquiv s).injective).mpr hy0

def IsDualPoly (c : ℂ) (p p' : ℂ[X]) : Prop :=
  p.coeff 0 ≠ 0 ∧ C (p.coeff 0) * p' = p.reverse.scaleRoots c

def GeoMatch {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {n l : ℕ} [Fact l.Prime]
    (ρ : G F Ω →* GL (Fin n) (Qbar l)) (ι : Qbar l →+* ℂ) (P : HeightOneSpectrum (𝓞 F) → ℂ[X]) : Prop :=
  ∀ᶠ v in cofinite, ∀ A σ, IsPlaceOver A v → IsFrob A (normV v) σ →
    ((ρ σ⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.map ι = P v

def dualGL {H R : Type} [Group H] [CommRing R] {n : ℕ} (ρ : H →* GL (Fin n) R) : H →* GL (Fin n) R where
  toFun g :=
    ⟨Matrix.transpose (((ρ g)⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R),
      Matrix.transpose ((ρ g : GL (Fin n) R) : Matrix (Fin n) (Fin n) R),
      by rw [← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.transpose_one],
      by rw [← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.transpose_one]⟩
  map_one' := by ext1; simp
  map_mul' a b := by
    ext1
    simp only [map_mul, _root_.mul_inv_rev, Units.val_mul, Matrix.transpose_mul]

theorem geoMatch_iff_frobMatch_dual {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    {n l : ℕ} [Fact l.Prime] (ρ : G F Ω →* GL (Fin n) (Qbar l)) (ι : Qbar l →+* ℂ)
    (P : HeightOneSpectrum (𝓞 F) → ℂ[X]) : GeoMatch ρ ι P ↔ FrobMatch (dualGL ρ) ι P := by
  unfold GeoMatch FrobMatch
  have h : ∀ σ : G F Ω, ((dualGL ρ σ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)).charpoly =
      ((ρ σ⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)).charpoly := by
    intro σ
    show (Matrix.transpose (((ρ σ)⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l))).charpoly = _
    rw [Matrix.charpoly_transpose, map_inv]
  simp only [h]

end TV

namespace VData

variable {D : D7} (V : VData D)

def IsRi {F : Type} [Field F] [NumberField F] [Algebra F TV.QbarQ] {n l : ℕ} [Fact l.Prime]
    (π : (V.spec F n).Rep) (ρ : Formalism.ConjugateSelfDual.G F TV.QbarQ →* GL (Fin n) (TV.QbarL l)) : Prop :=
  TV.GeoMatch ρ (V.iotaC l).toRingHom ((V.spec F n).hecke π)

def IsRACSDC (F : Type) [Field F] [NumberField F] (n : ℕ) (π : (V.spec F n).Rep) : Prop :=
  ∃ c : F ≃+* F, (∀ (τ : F →+* ℂ) (x : F), τ (c x) = (starRingEnd ℂ) (τ x)) ∧
    ∀ᶠ v in Filter.cofinite, TV.IsDualPoly ((Formalism.ConjugateSelfDual.normV v : ℂ) ^ (n - 1)) ((V.spec F n).hecke π v)
      ((V.spec F n).hecke π (TV.conjV c v))

def HasWt (s : VH.HidaSetting) (Pi : (V.spec s.L s.n).Rep) (lw : s.Weight) : Prop :=
  ∀ (v : s.Vl) (τ : s.Emb v) (j : Fin s.n),
    (V.spec s.L s.n).wt Pi ((V.iotaC s.l).toRingHom.comp
      (τ.1.comp (algebraMap s.L (IsDedekindDomain.HeightOneSpectrum.adicCompletion s.L (s.vt v))))) j =
      lw v τ j + ((j.rev : ℕ) : ℤ)

end VData

def eRange (D : D7) : Finset ℕ := Finset.Ico 1 D.R.t

def FactShaFinite {D : D7} (V : VData D) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ e ∈ eRange D, ∀ χ : TV.Chi D, V.Vlen l e χ ≠ ⊤

def LitShaEFinite {D : D7} (V : VData D) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ e ∈ eRange D, Module.length ℤ_[l] (V.shaE l e) ≠ ⊤

def BridgeShaN {D : D7} (V : VData D) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ e ∈ eRange D,
    Module.length ℤ_[l] (V.shaE l e) = Formalism.GaloisCohomology.shaLen (D.nd.ldat l) (e : ℤ)

def VchiSum {D : D7} (V : VData D) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ e ∈ eRange D,
    ∑ χ : TV.Chi D, V.Vq l e χ = D.what₂.shaLen l e

end Formalism.BasicNotions

namespace Formalism.BasicNotions

end Formalism.BasicNotions

namespace Formalism.BasicNotions

def VData.artVH {D : D7} (V : VData D) (s : VH.HidaSetting) : s.ArtAt :=
  fun v => V.artLoc s.L TV.QbarQ (s.vt v) (s.At v) (s.At_over v)

end Formalism.BasicNotions
