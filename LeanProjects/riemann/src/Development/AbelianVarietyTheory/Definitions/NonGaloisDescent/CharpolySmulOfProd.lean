import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.TameGeneratorProjectors
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.JumpDictionary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertialOrderFifteenCharAuxiliaryPrimeSpec
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PolarizedGaloisRep

noncomputable section

namespace GlobalTheory.Triple

open NumberField IsDedekindDomain Polynomial Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open Formalism.L2.Host (HChar CharFrame embLL0 eExp ValLL0)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
open GlobalTheory.GalChar (IsGal toQ block)
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (IsGaloisRepOf Zbar GalE toFb)
open GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary (embOver)

variable {D : D7}

section Reading

variable (X : NTw D.R D.host D.what₂ D.LL0 D.nd)

def embSide (i : X.Tw) (b : Bool) : ↥D.LL0 →+* FractionRing (X.O0 i) := if b then X.emb0 i else X.emb0b i

structure Reading (i : X.Tw) (b : Bool) where

  κ : FractionRing (X.O0 i) →+* Qbar (X.l i)

  ι : Qbar (X.l i) ≃+* ℂ
  κ_alg : ∀ z : ℤ_[X.l i], κ (algebraMap (X.O0 i) (FractionRing (X.O0 i)) (algebraMap ℤ_[X.l i] (X.O0 i) z)) =
    algebraMap ℚ_[X.l i] (Qbar (X.l i)) (z : ℚ_[X.l i])
  read : ∀ x : ↥D.LL0, ι (κ (embSide X i b x)) = embLL0 D x

variable {X} {i : X.Tw} {b : Bool}

def Reading.toC (ρ : Reading X i b) : X.O0 i →+* ℂ := ρ.ι.toRingHom.comp (toQ ρ.κ)

def Reading.Induces (ρ : Reading X i b) (w : D.what₂.places.Pl) : Prop :=
  ∀ x : D.what₂.LL, 0 ≤ D.what₂.places.val w x ↔ ‖ρ.ι.symm (D.what₂.embLL x)‖ ≤ 1

end Reading

def muBase (C : CharFrame D) (l : ℕ) (j : Fin D.R.m) : HChar D.host.E := C.mu0 j * C.delAt l

def blockChar (C : CharFrame D) (l : ℕ) (j : Fin D.R.m) : HChar D.host.E := block (muBase C l j) C.eta D.R.r

def shiftChar (C : CharFrame D) : HChar D.host.E := block 1 C.eta D.R.t

def rowPar {R : Ranks} (P : HCParam R) : Multiset ℚ :=
  (Finset.univ : Finset (Fin (R.k - 1))).val.map P.v + (Finset.univ : Finset (Fin R.m)).val.map fun a => -P.b a

def satake (μ : HChar D.host.E) (π : D.naut.CG D.R.r) (P : PlE D.host) : Multiset ℂ :=
  (D.naut.frobEig (D.naut.locG π P)).map fun a =>
    a⁻¹ * ((μ.val P : ℂˣ) : ℂ)⁻¹ * (((normV P : ℕ) : ℂ) ^ (D.R.nV / 2))⁻¹

def heckeVal (μ : HChar D.host.E) (π : D.naut.CG D.R.r) (k : ℕ) (P : PlE D.host) : ℂ :=
  ((normV P : ℕ) : ℂ) ^ (k * (D.R.r - k) / 2) * (satake μ π P).esymm k

abbrev FbAt (D : D7) (w : D.what₂.places.Pl) : Type :=
  Fb (D.what₂.places.resChar w) (D.what₂.places.resChar_prime w)

structure IsParam (σ : D.what₂.FT) (π : D.naut.CG D.R.r) : Prop where
  csd : D.naut.csd π
  ralg : D.naut.ralg π
  inf : ∀ τ : D.what₂.Tau, D.naut.infG π (embOver D τ false) = (rowPar (D.hc τ)).map (fun p => ((p : ℚ) : ℂ)) ∧
    D.naut.infG π (embOver D τ true) = (rowPar (D.hc τ)).map fun p => ((-p : ℚ) : ℂ)
  unr : ∀ w, (∀ k, w ∉ placesOver D.host.E (D.host.g k)) → D.naut.unr (D.naut.locG π w)
  lab : ∀ k v, D.nd.lab k σ v = D.naut.items₂ k (D.naut.plGw k v) (D.naut.locG π (D.naut.plGw k v))
  cusp : D.ntypes.cuspidal σ

structure IsResidual {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (r : GalE D →* GL (Fin D.R.r) (Qbar l)) (σ : D.what₂.FT)
    (w : D.what₂.places.Pl) (red : Zbar l →+* FbAt D w) : Prop where
  ss : IsSSRep (D.ntypes.rbar σ w)
  charpoly : ∀ g, ∃ p : (Zbar l)[X],
    p.map (Zbar l).subtype = ((r g : GL (Fin D.R.r) (Qbar l)) : Matrix (Fin D.R.r) (Fin D.R.r) (Qbar l)).charpoly ∧
    p.map red = ((D.ntypes.rbar σ w g : GL (Fin D.R.r) (FbAt D w)) : Matrix (Fin D.R.r) (Fin D.R.r) (FbAt D w)).charpoly
  teich : ∀ k, l ≠ D.host.g k → ∀ (v : D.nd.PlG k) x, x ≠ 0 → ∀ z : Zbar l,
    (z : Qbar l) = ι.symm (D.ntypes.teichC k x) → red z = D.ntypes.iota k v w x

section Comparison₂

variable (C : CharFrame D) (art : Ideles D.host.E →* Gab D.host.E D.nd.Om) {X : NTw D.R D.host D.what₂ D.LL0 D.nd}

def jIdx {i : X.Tw} (s : X.Sig i) : Fin D.R.m := ⟨X.jS i s - 1, by have := X.jS_range i s; omega⟩

structure IsChars {i : X.Tw} {b : Bool} (ρ : Reading X i b) : Prop where
  chi : ∀ j : Fin D.R.m, ∃ n, IsGal art ρ.κ ρ.ι (blockChar C (X.l i) j) n (X.chi1 i (j.1 + 1) b)
  tame : ∀ (j : Fin D.R.m) (k : Fin 2), X.l i ≠ D.host.g k → ∀ v : D.nd.PlG k, ∃ u : (ZMod (D.host.g k))ˣ,
    (u = D.nd.chiT k v j ∨ u = (D.nd.chiT k v j)⁻¹) ∧
    ρ.toC ((X.chi1 i (j.1 + 1) b (D.ntypes.tg k v) : (X.O0 i)ˣ) : X.O0 i) = D.ntypes.teichC k (toFb D k u)

structure IsTripleWith {i : X.Tw} {b : Bool} (ρ : Reading X i b) (s : X.Sig i) (σ : D.what₂.FT) (π : D.naut.CG D.R.r)
    (r : GalE D →* GL (Fin D.R.r) (Qbar (X.l i))) (ν : GalE D →* (X.O0 i)ˣ) (w : D.what₂.places.Pl)
    (red : Zbar (X.l i) →+* FbAt D w) : Prop where
  good : D.nd.goodRow σ
  occurs : D.what₂.isot (X.jS i s) σ ≠ ⊥
  param : IsParam σ π
  gal : IsGaloisRepOf D π (X.l i) ρ.ι r
  shift : ∃ n, IsGal art ρ.κ ρ.ι (shiftChar C) n ν
  rho : ∀ g, ((X.rhoS i s g : GL (Fin D.R.r) (X.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)).map (toQ ρ.κ) =
    toQ ρ.κ ((ν g : (X.O0 i)ˣ) : X.O0 i) •
      ((r g : GL (Fin D.R.r) (Qbar (X.l i))) : Matrix (Fin D.R.r) (Fin D.R.r) (Qbar (X.l i)))
  hecke : ∀ k P, k ≤ D.R.r → IsSplitPl D.host P → P ∉ X.S0 i → ∃ x : X.O0 i,
    algebraMap (X.O0 i) (X.O i) x = X.hEig i s k P ∧ ρ.toC x = heckeVal (muBase C (X.l i) (jIdx s)) π k P
  induces : ρ.Induces w
  residual : IsResidual ρ.ι r σ w red

def IsTripleAt {i : X.Tw} {b : Bool} (ρ : Reading X i b) (s : X.Sig i) : Prop :=
  ∃ σ π r ν w red, IsTripleWith C art ρ s σ π r ν w red

structure IsTripleFor (Y : NExp D.R D.host D.what₂ D.LL0 D.nd X) : Prop where
  artin : IsGlobalArtin art
  evidence : ∀ i, X.NonzeroIndexPlace i → ∀ b : Bool, ∃ ρ : Reading X i b, IsChars C art ρ ∧
    ∀ s : X.Sig i, X.side i s = b → IsTripleAt C art ρ s
  vec : ∀ i, X.NonzeroIndexPlace i → ∀ s : X.Sig i, Formalism.MainNotions.BlochKatoReduction.Gen.goodE Y i s
  all : Y.sig_all

end Comparison₂

def IsTripleOf {X : NTw D.R D.host D.what₂ D.LL0 D.nd} (Y : NExp D.R D.host D.what₂ D.LL0 D.nd X) : Prop :=
  ∃ (C : CharFrame D) (art : Ideles D.host.E →* Gab D.host.E D.nd.Om), IsTripleFor C art Y

def IsTriple (D : D7) : Prop := IsTripleOf D.nexp

section ReadingAPI

variable {X : NTw D.R D.host D.what₂ D.LL0 D.nd} {i : X.Tw} {b : Bool}

theorem Reading.toC_apply (ρ : Reading X i b) (x : X.O0 i) : ρ.toC x = ρ.ι (toQ ρ.κ x) := rfl

theorem Reading.toC_injective (ρ : Reading X i b) : Function.Injective ρ.toC :=
  ρ.ι.injective.comp (GlobalTheory.GalChar.toQ_injective ρ.κ)

theorem Reading.nonempty (i : X.Tw) (b : Bool) : Nonempty (Reading X i b) := by
  haveI : CharZero (FractionRing (X.O0 i)) := (X.emb0 i).charZero_iff (X.emb0 i).injective |>.1 inferInstance
  let f : ℤ_[X.l i] →+* FractionRing (X.O0 i) :=
    (algebraMap (X.O0 i) (FractionRing (X.O0 i))).comp (algebraMap ℤ_[X.l i] (X.O0 i))
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    by_contra h0
    rw [PadicInt.unitCoeff_spec h0, map_mul, map_pow, map_natCast] at hz
    rcases mul_eq_zero.1 hz with h | h
    · exact ((PadicInt.unitCoeff h0).isUnit.map f).ne_zero h
    · exact (pow_ne_zero _ (Nat.cast_ne_zero.2 (X.lPrime i).out.ne_zero)) h
  have hf0 : Function.Injective (algebraMap ℤ_[X.l i] (X.O0 i)) := Function.Injective.of_comp (f := algebraMap (X.O0 i) (FractionRing (X.O0 i))) hf
  haveI : Module.IsTorsionFree ℤ_[X.l i] (X.O0 i) := Module.isTorsionFree_iff_algebraMap_injective.2 hf0
  haveI : Module.IsTorsionFree ℤ_[X.l i] (Qbar (X.l i)) := Module.isTorsionFree_iff_algebraMap_injective.2
    (by rw [IsScalarTower.algebraMap_eq ℤ_[X.l i] ℚ_[X.l i] (Qbar (X.l i))]
        exact (algebraMap ℚ_[X.l i] (Qbar (X.l i))).injective.comp Subtype.val_injective)
  let g : X.O0 i →ₐ[ℤ_[X.l i]] Qbar (X.l i) := IsAlgClosed.lift
  have hg : Function.Injective g := by
    refine (RingHom.injective_iff_ker_eq_bot g.toRingHom).2 (Ideal.eq_bot_of_comap_eq_bot (R := ℤ_[X.l i]) ?_)
    rw [eq_bot_iff]
    intro z hz
    have h1 : algebraMap ℤ_[X.l i] (Qbar (X.l i)) z = 0 := (g.commutes z).symm.trans hz
    exact (map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).1 h1
  haveI : Countable ↥D.LL0 := (Module.finBasis ℚ ↥D.LL0).equivFun.injective.countable
  let κ : FractionRing (X.O0 i) →+* Qbar (X.l i) := IsFractionRing.lift (g := g.toRingHom) hg
  obtain ⟨ι, hι⟩ := GlobalTheory.exists_padicAlgCl_ringEquiv_complex_comp_eq_of_countable (X.l i) ↥D.LL0
    (κ.comp (embSide X i b)) (embLL0 D)
  exact ⟨⟨κ, ι, fun z => (IsFractionRing.lift_algebraMap hg _).trans (g.commutes z), hι⟩⟩

theorem Reading.Induces.resChar {ρ : Reading X i b} {w : D.what₂.places.Pl} (h : ρ.Induces w) :
    D.what₂.places.resChar w = X.l i := by
  by_contra hne
  have hp := D.what₂.places.resChar_prime w
  have h1 : ‖((D.what₂.places.resChar w : ℕ) : Qbar (X.l i))‖ = 1 := by
    rw [← map_natCast (algebraMap ℚ_[X.l i] (Qbar (X.l i))), norm_algebraMap', Padic.norm_natCast_eq_one_iff]
    exact (Nat.coprime_primes (X.lPrime i).out hp).2 (Ne.symm hne)
  have h2 := (h ((D.what₂.places.resChar w : ℕ) : D.what₂.LL)⁻¹).2 (by
    rw [map_inv₀, map_inv₀, map_natCast, map_natCast, norm_inv, h1, inv_one])
  have h3 := (D.what₂.places.val w).map_mul ((D.what₂.places.resChar w : ℕ) : D.what₂.LL)
    ((D.what₂.places.resChar w : ℕ) : D.what₂.LL)⁻¹
  rw [mul_inv_cancel₀ (Nat.cast_ne_zero.2 hp.ne_zero), AddValuation.map_one, D.what₂.places.val_resChar] at h3
  have h4 : (0 : WithTop ℤ) < (((D.what₂.places.ramIdx w : ℕ) : ℤ) : WithTop ℤ) := by
    exact_mod_cast D.what₂.places.ramIdx_pos w
  exact absurd h3 (lt_of_lt_of_le h4 (le_add_of_nonneg_right h2)).ne

end ReadingAPI

section Chars

variable (C : CharFrame D)

def hframe : GlobalTheory.Mem.Chr.HFrame D.host (fun j => eExp D j) :=
  ⟨C.P, C.W, C.mu0, C.eta, C.chiPsi, C.del, C.del', C.isMu0, C.isEta, C.isChi, C.isDel, C.isDel'⟩

theorem muBase_eq (l : ℕ) (j : Fin D.R.m) :
    muBase C l j = (hframe C).mu0 j * GlobalTheory.GalChar.delAt D.host (hframe C) l := rfl

theorem eExp_int (j : Fin D.R.m) (τ : D.R.Psi) : ∃ z : ℤ, eExp D j τ = z := (D.hc _).e_int j

theorem shiftChar_unr (v : PlE D.host) : (shiftChar C).UnrAt v := fun x hx => by
  rw [shiftChar, GlobalTheory.GalChar.block_loc (C.isEta.unr v) hx]
  rfl

theorem shiftChar_val (v : PlE D.host) : (((shiftChar C).val v : ℂˣ) : ℂ) =
    ((C.eta.val v : ℂˣ) : ℂ)⁻¹ * ((normV v : ℕ) : ℂ) ^ (((D.R.t : ℝ) / 2 : ℝ) : ℂ) := by
  rw [shiftChar, GlobalTheory.GalChar.block_val, one_mul, HChar.val_inv, Units.val_inv_eq_inv_val]
  rfl

theorem blockChar_val (l : ℕ) (j : Fin D.R.m) (v : PlE D.host) : (((blockChar C l j).val v : ℂˣ) : ℂ) =
    (((muBase C l j).val v : ℂˣ) : ℂ) * ((C.eta.val v : ℂˣ) : ℂ)⁻¹ * ((normV v : ℕ) : ℂ) ^ (((D.R.r : ℝ) / 2 : ℝ) : ℂ) := by
  rw [blockChar, GlobalTheory.GalChar.block_val, HChar.val_mul, HChar.val_inv, Units.val_mul, Units.val_inv_eq_inv_val]
  rfl

variable {C} {X : NTw D.R D.host D.what₂ D.LL0 D.nd} {i : X.Tw} {b : Bool} {art : Ideles D.host.E →* Gab D.host.E D.nd.Om}

theorem exists_shift (ha : IsGlobalArtin art) (hC : ValLL0 D C) (ρ : Reading X i b) :
    ∃ (ν : GalE D →* (X.O0 i)ˣ) (n : _), IsGal art ρ.κ ρ.ι (shiftChar C) n ν := by
  obtain ⟨n, hn⟩ := (GlobalTheory.Mem.CharAlg.isAlg_even_odd D.R D.host).2 C.eta C.isEta.inf D.R.t D.R.t_odd
  have h1 : GlobalTheory.HeckeGal.IsAlgPos (shiftChar C) n := by
    rw [shiftChar, block, one_mul]
    exact GlobalTheory.HeckeGal.isAlgPos_of_isAlg hn
  obtain ⟨ν, hν⟩ := GlobalTheory.GalChar.exists_isGal (X.twistBaseCoefficientRing_isAdic i) ρ.κ_alg ha h1 ρ.read
    (GlobalTheory.GalChar.AlmostIn.block (μ := 1) (Filter.Eventually.of_forall fun v => ⟨1, map_one _⟩) hC.eta D.R.t_odd)
  exact ⟨ν, n, hν⟩

theorem exists_blockChar (ha : IsGlobalArtin art) (hC : ValLL0 D C) (ρ : Reading X i b) (j : Fin D.R.m) :
    ∃ (χ : GalE D →* (X.O0 i)ˣ) (n : _), IsGal art ρ.κ ρ.ι (blockChar C (X.l i) j) n χ := by
  obtain ⟨n0, h0⟩ := GlobalTheory.GalChar.exists_isAlgPos_mu0 (hframe C) eExp_int j
  obtain ⟨n, hn⟩ := GlobalTheory.GalChar.block_alg (hframe C)
    ⟨_, GlobalTheory.GalChar.isAlgPos_mul h0 (GlobalTheory.GalChar.del_alg (hframe C) (X.l i))⟩
  have hδ : (C.delAt (X.l i)).ValuesIn 0 (embLL0 D) := by
    unfold CharFrame.delAt
    split_ifs
    exacts [hC.del', hC.del]
  obtain ⟨χ, hχ⟩ := GlobalTheory.GalChar.exists_isGal (X.twistBaseCoefficientRing_isAdic i) ρ.κ_alg ha hn ρ.read
    (((GlobalTheory.GalChar.almostIn_of_valuesIn (hC.mu0 j)).mul (GlobalTheory.GalChar.almostIn_of_valuesIn hδ)).block hC.eta
      (GlobalTheory.GalChar.odd_r D.R))
  exact ⟨χ, n, hχ⟩

end Chars

section Values

theorem card_rowPar {R : Ranks} (P : HCParam R) : Multiset.card (rowPar P) = R.r := by
  have h := R.m_add_three_le_k
  simp only [rowPar, Multiset.card_add, Multiset.card_map, Finset.card_val, Finset.card_univ, Fintype.card_fin, Ranks.r]
  omega

theorem param_eq {R : Ranks} (P : HCParam R) (j : Fin R.m) :
    GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.param P j = rowPar P + GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.run P j := rfl

theorem two_mul_nV_half (R : Ranks) : 2 * (R.nV / 2) = R.r + R.t :=
  Nat.two_mul_div_two_of_even ((GlobalTheory.GalChar.odd_r R).add_odd R.t_odd)

theorem two_mul_half (R : Ranks) {k : ℕ} (hk : k ≤ R.r) : 2 * (k * (R.r - k) / 2) = k * (R.r - k) := by
  refine Nat.two_mul_div_two_of_even ?_
  rcases Nat.even_or_odd k with h | h
  · exact h.mul_right _
  · exact (Nat.Odd.sub_odd (GlobalTheory.GalChar.odd_r R) h).mul_left _

theorem normV_ne_zero (P : PlE D.host) : ((normV P : ℕ) : ℂ) ≠ 0 := GlobalTheory.GalChar.absNorm_ne_zero P

variable (μ : HChar D.host.E) (π : D.naut.CG D.R.r) (P : PlE D.host)

theorem heckeVal_zero : heckeVal μ π 0 P = 1 := by simp [heckeVal, Multiset.esymm]

theorem card_satake (h : D.naut.unr (D.naut.locG π P)) : Multiset.card (satake μ π P) = D.R.r := by
  rw [satake, Multiset.card_map, D.naut.frobEig_card _ h, D.naut.locG_dim]

theorem heckeVal_top (h : D.naut.unr (D.naut.locG π P)) : heckeVal μ π D.R.r P = (satake μ π P).prod := by
  rw [heckeVal, Nat.sub_self, mul_zero, Nat.zero_div, pow_zero, one_mul, Multiset.esymm, ← card_satake μ π P h,
    Multiset.powersetCard_self]
  simp

theorem pow_mul_heckeVal {k : ℕ} (hk : k ≤ D.R.r) :
    ((normV P : ℕ) : ℂ) ^ (k * (k - 1) / 2) * heckeVal μ π k P =
      ((satake μ π P).map fun α => ((normV P : ℕ) : ℂ) ^ ((D.R.r - 1) / 2) * α).esymm k := by
  have e : k * (k - 1) / 2 + k * (D.R.r - k) / 2 = (D.R.r - 1) / 2 * k := by
    have h1 := two_mul_half D.R hk
    have h2 : 2 * (k * (k - 1) / 2) = k * (k - 1) := Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self k)
    obtain ⟨c, hc⟩ := GlobalTheory.GalChar.odd_r D.R
    have h3 : (D.R.r - 1) / 2 = c := by omega
    rcases k with _ | k
    · simp
    · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hk
      have h4 : D.R.r - (k + 1) = d := by omega
      rw [h3]
      rw [h4] at h1 ⊢
      rw [Nat.add_sub_cancel] at h2 ⊢
      have h5 : k + d = 2 * c := by omega
      have h6 : (k + 1) * k + (k + 1) * d = 2 * (c * (k + 1)) := by rw [← mul_add, h5]; ring
      omega
  rw [heckeVal, ← mul_assoc, ← pow_add, e, pow_mul]
  exact Multiset.pow_smul_esymm (((normV P : ℕ) : ℂ) ^ ((D.R.r - 1) / 2)) k (satake μ π P)

theorem geometric_eigenvalue (C : CharFrame D) (l : ℕ) (j : Fin D.R.m) (a : ℂ) :
    (a * ((normV P : ℕ) : ℂ) ^ (((1 - (D.R.r : ℝ)) / 2 : ℝ) : ℂ) * (((shiftChar C).val P : ℂˣ) : ℂ)⁻¹ *
        (((blockChar C l j).val P : ℂˣ) : ℂ) * ((normV P : ℕ) : ℂ) ^ D.R.t)⁻¹ =
      ((normV P : ℕ) : ℂ) ^ ((D.R.r - 1) / 2) *
        (a⁻¹ * (((muBase C l j).val P : ℂˣ) : ℂ)⁻¹ * (((normV P : ℕ) : ℂ) ^ (D.R.nV / 2))⁻¹) := by
  have hq := normV_ne_zero P
  set q : ℂ := ((normV P : ℕ) : ℂ)
  obtain ⟨c, hc⟩ := GlobalTheory.GalChar.odd_r D.R
  obtain ⟨d, hd⟩ := D.R.t_odd
  have h1 : (D.R.r - 1) / 2 = c := by omega
  have h2 : D.R.nV / 2 = c + d + 1 := by have := two_mul_nV_half D.R; omega
  have hs : q ^ (((1 / 2 : ℝ) : ℝ) : ℂ) ≠ 0 := by simp [hq]
  have e1 : q ^ (((1 - (D.R.r : ℝ)) / 2 : ℝ) : ℂ) = (q ^ c)⁻¹ := by
    rw [← Complex.cpow_natCast, ← Complex.cpow_neg, hc]; congr 1; push_cast; ring
  have e2 : ∀ n : ℕ, q ^ (((((2 * n + 1 : ℕ) : ℝ)) / 2 : ℝ) : ℂ) = q ^ n * q ^ (((1 / 2 : ℝ) : ℝ) : ℂ) := fun n => by
    rw [← Complex.cpow_natCast, ← Complex.cpow_add _ _ hq]; congr 1; push_cast; ring
  rw [shiftChar_val, blockChar_val, e1, h1, h2, hc, hd, e2, e2]
  have h3 := (C.eta.val P).ne_zero
  have h4 := ((muBase C l j).val P).ne_zero
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  · field_simp
    ring

end Values

section API

theorem charpoly_smul_of_prod {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (m : Multiset ℂ) (c : ℂ)
    (h : M.charpoly = (m.map fun a => X - C a).prod) : (c • M).charpoly = (m.map fun a => X - C (a * c)).prod := by
  have hn : Multiset.card m = n := by
    have := congrArg natDegree h
    rwa [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin, natDegree_multiset_prod_X_sub_C_eq_card, eq_comm] at this
  rcases eq_or_ne c 0 with rfl | hc
  · simp [hn]
  · apply Polynomial.funext
    intro z
    have h1 := congrArg (eval (z / c)) h
    rw [Matrix.eval_charpoly, eval_multiset_prod, Multiset.map_map] at h1
    have e : Matrix.scalar (Fin n) z - c • M = c • (Matrix.scalar (Fin n) (z / c) - M) := by
      rw [smul_sub, Matrix.scalar_apply, Matrix.scalar_apply, ← Matrix.diagonal_smul]
      congr 2
      funext x
      simp [mul_div_cancel₀ _ hc]
    rw [Matrix.eval_charpoly, eval_multiset_prod, Multiset.map_map, e, Matrix.det_smul, h1, Fintype.card_fin, ← hn,
      ← Multiset.prod_replicate, ← Multiset.map_const', ← Multiset.prod_map_mul]
    refine congrArg _ (Multiset.map_congr rfl fun a _ => ?_)
    simp only [Function.comp_apply, eval_sub, eval_X, eval_C]
    field_simp

theorem isGaloisRepOf_conj {a : ℕ} {π : D.naut.CG a} {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ}
    {r r' : GalE D →* GL (Fin a) (Qbar l)} (h : IsGaloisRepOf D π l ι r) (A : GL (Fin a) (Qbar l))
    (hA : ∀ g, r' g = A * r g * A⁻¹) : IsGaloisRepOf D π l ι r' := by
  have hc : ∀ g, ((r' g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly =
      ((r g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly := fun g => by
    rw [hA, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj]
  refine ⟨?_, GlobalTheory.Proof.SemisimpleRepresentationIntegralConjugate.isSSRep_conj A hA h.2.1, fun w hw => ⟨fun s hs => ?_, ?_, fun hu B s hB hs => ?_⟩⟩
  · simp only [hA, Units.val_mul]
    exact (continuous_const.mul h.1).mul continuous_const
  · rw [hc]; exact (h.2.2 w hw).1 s hs
  · rw [(h.2.2 w hw).2.1, show (r' : GalE D → _) = (MulAut.conj A) ∘ r from funext hA, Set.image_comp]
    exact (Set.finite_image_iff (MulAut.conj A).injective.injOn).symm
  · rw [hc]; exact (h.2.2 w hw).2.2 hu B s hB hs

variable {C : CharFrame D} {art : Ideles D.host.E →* Gab D.host.E D.nd.Om} {X : NTw D.R D.host D.what₂ D.LL0 D.nd}
  {i : X.Tw} {b : Bool} {ρ : Reading X i b} {s : X.Sig i} {σ : D.what₂.FT} {π : D.naut.CG D.R.r}
  {r : GalE D →* GL (Fin D.R.r) (Qbar (X.l i))} {ν : GalE D →* (X.O0 i)ˣ} {w : D.what₂.places.Pl}
  {red : Zbar (X.l i) →+* FbAt D w}

theorem isTripleAt_of_conj (good : D.nd.goodRow σ) (occurs : D.what₂.isot (X.jS i s) σ ≠ ⊥) (param : IsParam σ π)
    (gal : IsGaloisRepOf D π (X.l i) ρ.ι r) (shift : ∃ n, IsGal art ρ.κ ρ.ι (shiftChar C) n ν)
    (A : GL (Fin D.R.r) (Qbar (X.l i)))
    (rho : ∀ g, ((X.rhoS i s g : GL (Fin D.R.r) (X.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)).map (toQ ρ.κ) =
      toQ ρ.κ ((ν g : (X.O0 i)ˣ) : X.O0 i) •
        ((A * r g * A⁻¹ : GL (Fin D.R.r) (Qbar (X.l i))) : Matrix (Fin D.R.r) (Fin D.R.r) (Qbar (X.l i))))
    (hecke : ∀ k P, k ≤ D.R.r → IsSplitPl D.host P → P ∉ X.S0 i → ∃ x : X.O0 i,
      algebraMap (X.O0 i) (X.O i) x = X.hEig i s k P ∧ ρ.toC x = heckeVal (muBase C (X.l i) (jIdx s)) π k P)
    (induces : ρ.Induces w) (residual : IsResidual ρ.ι r σ w red) : IsTripleAt C art ρ s := by
  refine ⟨σ, π, (MulAut.conj A).toMonoidHom.comp r, ν, w, red, good, occurs, param,
    isGaloisRepOf_conj gal A fun _ => rfl, shift, rho, hecke, induces, residual.ss, fun g => ?_, residual.teich⟩
  obtain ⟨p, h1, h2⟩ := residual.charpoly g
  refine ⟨p, h1.trans ?_, h2⟩
  change _ = ((A * r g * A⁻¹ : GL (Fin D.R.r) (Qbar (X.l i))) : Matrix (Fin D.R.r) (Fin D.R.r) (Qbar (X.l i))).charpoly
  rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj]

theorem jIdx_add_one (s : X.Sig i) : (jIdx s).1 + 1 = X.jS i s := by
  have := X.jS_range i s
  simp only [jIdx]
  omega

theorem IsChars.chiS {ρ : Reading X i (X.side i s)} (h : IsChars C art ρ) :
    ∃ n, IsGal art ρ.κ ρ.ι (blockChar C (X.l i) (jIdx s)) n (Formalism.MainNotions.BlochKatoReduction.Gen.chiS i s) := by
  have := h.chi (jIdx s)
  rwa [jIdx_add_one] at this

theorem IsTripleWith.hEig_zero (h : IsTripleWith C art ρ s σ π r ν w red) {P : PlE D.host} (hP : IsSplitPl D.host P)
    (hS : P ∉ X.S0 i) : X.hEig i s 0 P = 1 := by
  obtain ⟨x, h1, h2⟩ := h.hecke 0 P (Nat.zero_le _) hP hS
  rw [heckeVal_zero, ← map_one ρ.toC] at h2
  rw [← h1, ρ.toC_injective h2, map_one]

theorem IsTripleWith.unr_of_notMem (h : IsTripleWith C art ρ s σ π r ν w red) {P : PlE D.host} (hS : P ∉ X.S0 i) :
    D.naut.unr (D.naut.locG π P) := h.param.unr P fun k hk => hS (X.placesOver_subset_exceptional i k hk)

theorem IsTripleWith.charpoly_frob (ha : IsGlobalArtin art) (h : IsTripleWith C art ρ s σ π r ν w red) {P : PlE D.host}
    (hl : P ∉ placesOver D.host.E (X.l i)) (hg : ∀ k, P ∉ placesOver D.host.E (D.host.g k))
    {B : ValuationSubring D.nd.Om} (hB : IsPlaceOver B P) {g : GalE D} (hF : IsFrob (F := D.host.E) B (normV P) g) :
    ((X.rhoS i s g : GL (Fin D.R.r) (X.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)).charpoly.map ρ.toC =
      ((D.naut.frobEig (D.naut.locG π P)).map fun a => Polynomial.X - Polynomial.C
        (a * ((normV P : ℕ) : ℂ) ^ (((1 - (D.R.r : ℝ)) / 2 : ℝ) : ℂ) * (((shiftChar C).val P : ℂˣ) : ℂ)⁻¹)).prod := by
  have hu := h.param.unr P hg
  obtain ⟨n, hn⟩ := h.shift
  have e1 := (h.gal.2.2 P hl).2.2 hu B g hB hF
  have e2 := hn.frob ha (Or.inl hl) (shiftChar_unr C P) hB hF
  rw [galPol, D.naut.frobEig_tw _ _ hu, ← Matrix.charpoly_map] at e1
  have e3 : ((X.rhoS i s g : GL (Fin D.R.r) (X.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)).map ρ.toC =
      (((shiftChar C).val P : ℂˣ) : ℂ)⁻¹ •
        ((r g : GL (Fin D.R.r) (Qbar (X.l i))) : Matrix (Fin D.R.r) (Fin D.R.r) (Qbar (X.l i))).map ρ.ι.toRingHom := by
    ext x y
    have := congrArg ρ.ι (congrFun (congrFun (h.rho g) x) y)
    simpa [e2, Reading.toC_apply] using this
  rw [← Matrix.charpoly_map, e3, charpoly_smul_of_prod _ _ _ e1, Multiset.map_map]
  rfl

variable {Y : NExp D.R D.host D.what₂ D.LL0 D.nd X}

theorem IsTripleFor.triple (h : IsTripleFor C art Y) {i : X.Tw} (hi : X.NonzeroIndexPlace i) (s : X.Sig i) :
    ∃ ρ : Reading X i (X.side i s), IsChars C art ρ ∧ IsTripleAt C art ρ s :=
  let ⟨ρ, h1, h2⟩ := h.evidence i hi (X.side i s)
  ⟨ρ, h1, h2 s rfl⟩

theorem IsTripleOf.allGood (h : IsTripleOf Y) : GlobalTheory.TwSys.AllGood Y := let ⟨_, _, h⟩ := h; h.vec

theorem IsTripleOf.sig_all (h : IsTripleOf Y) : Y.sig_all := let ⟨_, _, h⟩ := h; h.all

end API

end GlobalTheory.Triple

end
