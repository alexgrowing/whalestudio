import Mathlib
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.ExampleSatisfiesConditionsAtFive
import Formalism.LocalRingCardinality.DataParams

open NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters

open Formalism.BasicNotions Formalism.L2.Indef Formalism.L2.Indef.Tree

section LocalGroups

variable (r : ℕ) (k : Type) [Field k]

def mirabolic : Subgroup (GL (Fin r) k) where
  carrier := {h | ∀ i : Fin r, i.val + 1 = r → ∀ j, (h : Matrix (Fin r) (Fin r) k) i j = if i = j then 1 else 0}
  one_mem' := by
    intro i _ j
    simp [Matrix.one_apply]
  mul_mem' := by
    intro a b ha hb i hi j
    simp [Matrix.mul_apply, ha i hi, hb i hi]
  inv_mem' := by
    intro a ha i hi j
    have h : ((a : Matrix (Fin r) (Fin r) k) * ((a⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k)) i j =
        (1 : Matrix (Fin r) (Fin r) k) i j := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    rw [← h]
    simp [ha i hi]

theorem diag_mul_of_upper {r : ℕ} {k : Type} [Field k] (A B : Matrix (Fin r) (Fin r) k)
    (hA : A.BlockTriangular id) (hB : B.BlockTriangular id) (i : Fin r) : (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single i (fun j _ hj => ?_) (fun h => absurd (Finset.mem_univ i) h)
  rcases lt_or_gt_of_ne hj with h | h
  · rw [hA (show id j < id i from h), zero_mul]
  · rw [hB (show id i < id j from h), mul_zero]

def unitri : Subgroup (GL (Fin r) k) where
  carrier := {u | (u : Matrix (Fin r) (Fin r) k).BlockTriangular id ∧ ∀ i, (u : Matrix (Fin r) (Fin r) k) i i = 1}
  one_mem' := ⟨by simpa using Matrix.blockTriangular_one, fun i => by simp⟩
  mul_mem' := by
    intro a b ha hb
    refine ⟨by simpa using ha.1.mul hb.1, fun i => ?_⟩
    rw [Units.val_mul, diag_mul_of_upper _ _ ha.1 hb.1, ha.2, hb.2, one_mul]
  inv_mem' := by
    intro a ha
    have h1 : ((a⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k).BlockTriangular id := by
      letI := a.invertible
      rw [Matrix.coe_units_inv]
      exact Matrix.blockTriangular_inv_of_blockTriangular ha.1
    refine ⟨h1, fun i => ?_⟩
    have h := diag_mul_of_upper _ _ ha.1 h1 i
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one, ha.2, one_mul, Matrix.one_apply_eq] at h
    exact h.symm

variable {r k}

def superDiag (u : Matrix (Fin r) (Fin r) k) : k :=
  ∑ i : Fin r, ∑ j : Fin r, if j.val = i.val + 1 then u i j else 0

example (a : k) : superDiag !![1, a; 0, 1] = a := by
  simp [superDiag, Fin.sum_univ_two]

end LocalGroups

section Idem

variable {K : Type} [Field K] {G : Type} [Group G]

def IsIrrCharacter (τ : G → K) : Prop :=
  ∃ (n : ℕ) (ρ : Representation (AlgebraicClosure K) G (Fin n → AlgebraicClosure K)),
    ρ.IsIrreducible ∧ ∀ a, LinearMap.trace _ _ (ρ a) = algebraMap K (AlgebraicClosure K) (τ a)

def centralIdem [Finite G] (τ : G → K) : MonoidAlgebra K G :=
  haveI := Fintype.ofFinite G
  ∑ a : G, MonoidAlgebra.single a (τ 1 / (Nat.card G : K) * τ a⁻¹)

def twistInv (χ : G →* Kˣ) : MonoidAlgebra K G →ₐ[K] MonoidAlgebra K G :=
  MonoidAlgebra.lift K (MonoidAlgebra K G) G
    { toFun := fun a => MonoidAlgebra.single a (((χ a)⁻¹ : Kˣ) : K)
      map_one' := by simp [MonoidAlgebra.one_def]
      map_mul' := fun a b => by simp [MonoidAlgebra.single_mul_single, mul_comm] }

example (χ : G →* Kˣ) (a : G) :
    twistInv χ (MonoidAlgebra.single a 1) = MonoidAlgebra.single a (((χ a)⁻¹ : Kˣ) : K) := by
  simp [twistInv]

end Idem

section Types

variable (p : ℕ) [hp : Fact p.Prime]

abbrev Fbar : Type := AlgebraicClosure (ZMod p)

abbrev Tor (d : ℕ) : Subgroup (Fbar p)ˣ := rootsOfUnity (p ^ d - 1) (Fbar p)

def torNorm {d D : ℕ} (h : d ∣ D) : Tor p D →* Tor p d :=
  ((powMonoidHom ((p ^ D - 1) / (p ^ d - 1))).comp (Tor p D).subtype).codRestrict (Tor p d) (by
    intro x
    have hx := x.2
    rw [mem_rootsOfUnity] at hx ⊢
    show (x.1 ^ ((p ^ D - 1) / (p ^ d - 1))) ^ (p ^ d - 1) = 1
    rw [← pow_mul, Nat.div_mul_cancel (Nat.pow_sub_one_dvd_pow_sub_one p h), hx])

def toTorOne : (ZMod p)ˣ →* Tor p 1 :=
  (Units.map (algebraMap (ZMod p) (Fbar p) : ZMod p →* Fbar p)).codRestrict (Tor p 1) (by
    intro a
    rw [mem_rootsOfUnity, ← map_pow, pow_one, ZMod.units_pow_card_sub_one_eq_one, map_one])

theorem toTorOne_bijective : Function.Bijective (toTorOne p) := by
  constructor
  · intro a b h
    have h1 := congrArg (fun x : Tor p 1 => ((x : (Fbar p)ˣ) : Fbar p)) h
    exact Units.ext ((algebraMap (ZMod p) (Fbar p)).injective h1)
  · intro x
    have hx := x.2
    rw [mem_rootsOfUnity, pow_one] at hx
    have h2 : ((x : (Fbar p)ˣ) : Fbar p) ^ p = ((x : (Fbar p)ˣ) : Fbar p) := by
      have h3 : ((x : (Fbar p)ˣ) : Fbar p) ^ (p - 1) = 1 := by
        rw [← Units.val_pow_eq_pow_val, hx, Units.val_one]
      have h4 : p = (p - 1) + 1 := (Nat.sub_add_cancel hp.out.one_le).symm
      calc ((x : (Fbar p)ˣ) : Fbar p) ^ p = ((x : (Fbar p)ˣ) : Fbar p) ^ ((p - 1) + 1) := by rw [← h4]
        _ = _ := by rw [pow_succ, h3, one_mul]
    obtain ⟨n, hn⟩ := (mem_bot_iff_intCast p (Fbar p)).1 ((Subfield.mem_bot_iff_pow_eq_self (Fbar p) p).2 h2)
    have hn' : algebraMap (ZMod p) (Fbar p) (n : ZMod p) = ((x : (Fbar p)ˣ) : Fbar p) := by rw [map_intCast, hn]
    have h0 : (n : ZMod p) ≠ 0 := by
      intro h
      rw [h, map_zero] at hn'
      exact (x : (Fbar p)ˣ).ne_zero hn'.symm
    exact ⟨Units.mk0 _ h0, Subtype.ext (Units.ext hn')⟩

def baseNorm (D : ℕ) : Tor p D →* (ZMod p)ˣ :=
  ((MulEquiv.ofBijective (toTorOne p) (toTorOne_bijective p)).symm : Tor p 1 →* (ZMod p)ˣ).comp (torNorm p (one_dvd D))

variable {p} {K : Type} [Field K]

def torVal {d : ℕ} (θ : Tor p d →* Kˣ) : Fbar p → K :=
  Function.extend (fun u : Tor p d => ((u : (Fbar p)ˣ) : Fbar p)) (fun u => ((θ u : Kˣ) : K)) 0

open Classical in

def cuspChar {ι : Type} [Fintype ι] [DecidableEq ι] (θ : Tor p (Fintype.card ι) →* Kˣ) (h : Matrix ι ι (ZMod p)) : K :=
  if ∃ (φ : (ZMod p)[X]) (n : ℕ), Irreducible φ ∧ h.charpoly = φ ^ n then
    (-1) ^ (Fintype.card ι - 1) * ∑ z ∈ (h.charpoly.aroots (Fbar p)).toFinset, torVal θ z *
      ∏ i ∈ Finset.Ico 1 (Module.finrank (Fbar p)
          (Module.End.eigenspace (Matrix.toLin' (h.map (algebraMap (ZMod p) (Fbar p)))) z)),
        (1 - (p : K) ^ ((h.charpoly.aroots (Fbar p)).toFinset.card * i))
  else 0

abbrev Cyc {r : ℕ} (b : Fin r → Fin r) : Type := {c : Fin r // ∃ i, b i = c}

abbrev cycLen {r : ℕ} (b : Fin r → Fin r) (c : Cyc b) : ℕ := Fintype.card {i : Fin r // b i = c.1}

theorem cycLen_pos {r : ℕ} (b : Fin r → Fin r) (c : Cyc b) : 0 < cycLen b c := by
  obtain ⟨i, hi⟩ := c.2
  exact Fintype.card_pos_iff.2 ⟨⟨i, hi⟩⟩

theorem cycLen_dvd {r : ℕ} (b : Fin r → Fin r) (c : Cyc b) : cycLen b c ∣ r.factorial :=
  Nat.dvd_factorial (cycLen_pos b c) (by simpa using Fintype.card_subtype_le (fun i : Fin r => b i = c.1))

variable (p K) in

abbrev SSParam (r : ℕ) : Type := Σ b : Fin r → Fin r, ∀ c : Cyc b, (Tor p (cycLen b c) →* Kˣ)

instance finiteTor {r : ℕ} (b : Fin r → Fin r) (c : Cyc b) : Finite (Tor p (cycLen b c)) := by
  have : NeZero (p ^ cycLen b c - 1) :=
    ⟨(Nat.sub_pos_of_lt (Nat.one_lt_pow (cycLen_pos b c).ne' hp.out.one_lt)).ne'⟩
  infer_instance

instance finiteSSParam (r : ℕ) : Finite (SSParam p K r) := by
  have : ∀ (b : Fin r → Fin r) (c : Cyc b), Finite (Tor p (cycLen b c) →* Kˣ) := fun b c => by
    infer_instance
  infer_instance

variable {r : ℕ}

def cycChar (s : SSParam p K r) (c : Cyc s.1) : Tor p r.factorial →* Kˣ :=
  (s.2 c).comp (torNorm p (cycLen_dvd s.1 c))

def rootChar (s : SSParam p K r) (x : Σ c : Cyc s.1, Fin (cycLen s.1 c)) : Tor p r.factorial →* Kˣ :=
  cycChar s x.1 ^ (p ^ x.2.val)

open Classical in

def typeChar (s : SSParam p K r) (x : GL (Fin r) (ZMod p)) : K :=
  haveI := Fintype.ofFinite (GL (Fin r) (ZMod p))
  ((Nat.card {y : GL (Fin r) (ZMod p) // (y : Matrix (Fin r) (Fin r) (ZMod p)).BlockTriangular s.1} : ℕ) : K)⁻¹ *
    ∑ y : GL (Fin r) (ZMod p),
      if ((y⁻¹ * x * y : GL (Fin r) (ZMod p)) : Matrix (Fin r) (Fin r) (ZMod p)).BlockTriangular s.1 then
        ∏ c : Cyc s.1, cuspChar (s.2 c)
          (((y⁻¹ * x * y : GL (Fin r) (ZMod p)) : Matrix (Fin r) (Fin r) (ZMod p)).toSquareBlock s.1 c.1)
      else 0

def CongrMod {A : Type} [CommGroup A] (l : ℕ) (x y : A) : Prop := ∃ n : ℕ, (x / y) ^ (l ^ n) = 1

def BB (g r : ℕ) : Set ℕ :=
  {l | l = g ∨ (l.Prime ∧ ∃ a, 1 ≤ a ∧ a ≤ r ∧ g ^ a < (l ^ padicValNat l (g ^ a - 1)) ^ 4)}

def IsRegularParam (s : SSParam p K r) : Prop := Function.Injective (rootChar s)

def GoodAt {ι J : Type} (χ : J → ((ZMod p)ˣ →* Kˣ)) (s : ι → SSParam p K r) : Prop :=

  (∀ v, IsRegularParam (s v)) ∧

  (∀ l : ℕ, l.Prime → l ∉ BB p r → ∀ v, ∀ x y, x ≠ y → ¬ CongrMod l (rootChar (s v) x) (rootChar (s v) y)) ∧

  ((∀ l : ℕ, l.Prime → l ≠ p → ∀ v j c,
      ¬ CongrMod l (cycChar (s v) c) ((χ j).comp (baseNorm p r.factorial)) ∧
      ¬ CongrMod l (cycChar (s v) c) ((χ j)⁻¹.comp (baseNorm p r.factorial))) ∧
    ∀ v j x, rootChar (s v) x ≠ (χ j).comp (baseNorm p r.factorial) ∧
      rootChar (s v) x ≠ (χ j)⁻¹.comp (baseNorm p r.factorial)) ∧

  (¬ ∃ a : ℕ, 1 ≤ a ∧ 2 * a ≤ r ∧ ∀ v, ∃ A : Finset (Cyc (s v).1), ∑ c ∈ A, cycLen (s v).1 c = a) ∧

  ∃ v, ∃ c : Cyc (s v).1, (cycLen (s v).1 c).Prime ∧ r < 2 * cycLen (s v).1 c ∧ cycLen (s v).1 c + 3 ≤ r

end Types

section Level

variable {R : Ranks} (H : Host R)

instance factPrime (i : Fin 2) : Fact (H.g i).Prime := ⟨H.g_prime i⟩

def PlOver (i : Fin 2) : Type := {v : HeightOneSpectrum (𝓞 H.F) // ((H.g i : ℕ) : 𝓞 H.F) ∈ v.asIdeal}

instance finitePlOver (i : Fin 2) : Finite (PlOver H i) := by
  have h0 : (Ideal.span {((H.g i : ℕ) : 𝓞 H.F)}) ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast (H.g_prime i).ne_zero
  have h := Ideal.finite_factors h0
  refine Set.Finite.to_subtype (s := {v : HeightOneSpectrum (𝓞 H.F) | ((H.g i : ℕ) : 𝓞 H.F) ∈ v.asIdeal}) (h.subset ?_)
  intro v hv
  exact Ideal.dvd_span_singleton.2 hv

abbrev Sq : Type := Σ i : Fin 2, PlOver H i

abbrev LevelGroup : Type := ∀ v : Sq H, GL (Fin R.r) (ZMod (H.g v.1))

def levelU : Subgroup (LevelGroup H) := Subgroup.pi Set.univ fun v => unitri R.r (ZMod (H.g v.1))

def levelP : Subgroup (LevelGroup H) := Subgroup.pi Set.univ fun v => mirabolic R.r (ZMod (H.g v.1))

def levelUP : Subgroup (levelP H) := (levelU H).subgroupOf (levelP H)

def delq : ℕ := (levelUP H).index

variable {H} {K : Type} [Field K]

def IsGenericFamily {A : Type} [CommMonoid A] (ψ : ∀ v : Sq H, AddChar (ZMod (H.g v.1)) A) : Prop := ∀ v, ψ v ≠ 1

def psiU {A : Type} [CommMonoid A] (ψ : ∀ v : Sq H, AddChar (ZMod (H.g v.1)) A) (u : LevelGroup H) : A :=
  haveI := Fintype.ofFinite (Sq H)
  ∏ v : Sq H, ψ v (superDiag ((u v : GL (Fin R.r) (ZMod (H.g v.1))) : Matrix (Fin R.r) (Fin R.r) (ZMod (H.g v.1))))

def IsGeneratorFamily (om : ∀ i : Fin 2, (ZMod (H.g i))ˣ →* Kˣ) : Prop := ∀ i, Function.Injective (om i)

def chiTame (om : ∀ i : Fin 2, (ZMod (H.g i))ˣ →* Kˣ) (i : Fin 2) (j : Fin R.m) : (ZMod (H.g i))ˣ →* Kˣ :=
  om i ^ (2 * (j.val + 1))

def chiDet (om : ∀ i : Fin 2, (ZMod (H.g i))ˣ →* Kˣ) (j : Fin R.m) : LevelGroup H →* Kˣ :=
  haveI := Fintype.ofFinite (Sq H)
  ∏ v : Sq H, ((chiTame om v.1 j).comp Matrix.GeneralLinearGroup.det).comp
    (Pi.evalMonoidHom (fun v : Sq H => GL (Fin R.r) (ZMod (H.g v.1))) v)

def IsGoodParam (om : ∀ i : Fin 2, (ZMod (H.g i))ˣ →* Kˣ) (s : ∀ v : Sq H, SSParam (H.g v.1) K R.r) : Prop :=
  ∀ i : Fin 2, GoodAt (chiTame om i) (fun w : PlOver H i => s ⟨i, w⟩)

def tupleChar (s : ∀ v : Sq H, SSParam (H.g v.1) K R.r) (a : LevelGroup H) : K :=
  haveI := Fintype.ofFinite (Sq H)
  ∏ v : Sq H, typeChar (s v) (a v)

def goodTypes (om : ∀ i : Fin 2, (ZMod (H.g i))ˣ →* Kˣ) : Set (LevelGroup H → K) :=
  tupleChar '' {s | IsGoodParam om s}

theorem goodTypes_finite (om : ∀ i : Fin 2, (ZMod (H.g i))ˣ →* Kˣ) : (goodTypes om).Finite :=
  (Set.toFinite _).image _

def goodIdem (om : ∀ i : Fin 2, (ZMod (H.g i))ˣ →* Kˣ) : MonoidAlgebra K (LevelGroup H) :=
  ∑ τ ∈ (goodTypes_finite om).toFinset, centralIdem τ

def goodIdemTw (om : ∀ i : Fin 2, (ZMod (H.g i))ˣ →* Kˣ) (j : Fin R.m) : MonoidAlgebra K (LevelGroup H) :=
  twistInv (chiDet om j) (goodIdem om)

variable (H K) in

def HasLevelRoots : Prop := ∃ ζ : K, IsPrimitiveRoot ζ (Nat.card (LevelGroup H))

end Level

section Ties

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Df : DefSide Bs} {S : IndefData Df} {c : OnConst}

def TieGroup {R : Ranks} {H : Host R} (ψ : ∀ v : Sq H, AddChar (ZMod (H.g v.1)) (𝓞 K)) (O : OnObj S (levelP H) c) : Prop :=
  O.U = levelUP H ∧ ∀ u : levelP H, u ∈ levelUP H → O.ψ u = psiU ψ (u : LevelGroup H)

def TieAction {R : Ranks} {H : Host R} (om : ∀ i : Fin 2, (ZMod (H.g i))ˣ →* Kˣ) (jx : Bs.J ≃ Fin R.m)
    (O : OnObj S (levelP H) c) (ρ₀ : ∀ j, Representation K (LevelGroup H) (Fin (O.nZ j) → K)) : Prop :=
  ∀ j, O.ρ j = (ρ₀ j).comp (levelP H).subtype ∧
    O.e j = (ρ₀ j).asAlgebraHom (goodIdemTw om (jx j)) ∧
    O.V₀ j = LinearMap.range ((ρ₀ j).asAlgebraHom (goodIdemTw om (jx j)))

def TieNumbers {D : D7} (L : SizeData₂ D) {P : Type} [Group P] [Finite P] (O : OnObj S P c) : Prop :=
  O.g1 = D.host.g 0 ∧ O.g2 = D.host.g 1 ∧ O.f = (D.R.f : ℝ) ∧ O.k = (D.R.k : ℝ) ∧ O.m = (D.R.m : ℝ) ∧
    O.rr = (D.R.r : ℝ) ∧ O.x = L.sc.x ∧ O.eps = L.sc.eps

def LevelTie {D : D7} (L : SizeData₂ D) (ψ : ∀ v : Sq D.host, AddChar (ZMod (D.host.g v.1)) (𝓞 K))
    (om : ∀ i : Fin 2, (ZMod (D.host.g i))ˣ →* Kˣ) (jx : Bs.J ≃ Fin D.R.m)
    (O : OnObj S (levelP D.host) c) (ρ₀ : ∀ j, Representation K (LevelGroup D.host) (Fin (O.nZ j) → K)) : Prop :=
  HasLevelRoots D.host K ∧ IsGenericFamily ψ ∧ IsGeneratorFamily om ∧
    TieGroup ψ O ∧ TieAction om jx O ρ₀ ∧ TieNumbers L O

end Ties

def ClaimPlaces : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (_ : ParameterChoice' D L),
    Function.Injective (fun v : Sq D.host => v.2.1) ∧
    Set.range (fun v : Sq D.host => v.2.1) =
      {v : HeightOneSpectrum (𝓞 D.host.F) | ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal} ∧
    (∀ i, Nat.card (PlOver D.host i) = D.R.f) ∧ Nat.card (Sq D.host) = 2 * D.R.f ∧
    ∀ v : Sq D.host, Nat.card (𝓞 D.host.F ⧸ v.2.1.asIdeal) = D.host.g v.1

def ClaimCharacter : Prop :=
  ∀ (R : Ranks) (H : Host R) (A : Type) [CommMonoid A] (ψ : ∀ v : Sq H, AddChar (ZMod (H.g v.1)) A),
    levelU H ≤ levelP H ∧ psiU ψ 1 = 1 ∧
    (∀ u ∈ levelU H, ∀ u' ∈ levelU H, psiU ψ (u * u') = psiU ψ u * psiU ψ u') ∧
    ∀ u ∈ levelU H, psiU ψ u ^ (H.g 0 * H.g 1) = 1

def ClaimLocalOrders : Prop :=
  ∀ (r : ℕ) (k : Type) [Field k] [Finite k], 1 ≤ r →
    Nat.card (unitri r k) = Nat.card k ^ (r * (r - 1) / 2) ∧
    Nat.card (mirabolic r k) = Nat.card k ^ (r * (r - 1) / 2) * ∏ i ∈ Finset.Ico 1 r, (Nat.card k ^ i - 1) ∧
    ((unitri r k).subgroupOf (mirabolic r k)).index = ∏ i ∈ Finset.Ico 1 r, (Nat.card k ^ i - 1)

def ClaimIndex : Prop :=
  ∀ (R : Ranks) (H : Host R),
    haveI := Fintype.ofFinite (Sq H)
    delq H = ∏ v : Sq H, ∏ i ∈ Finset.Ico 1 R.r, (H.g v.1 ^ i - 1)

def ClaimPageBound : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (_ : ParameterChoice' D L),
    (1 : ℝ) / 2 ≤ 1 - 1 / (4 * ((D.R.f : ℝ) * D.R.k) ^ 3) ∧
    1 - 1 / (4 * ((D.R.f : ℝ) * D.R.k) ^ 3) ≤ (delq D.host : ℝ) / (Nat.card (levelU D.host) : ℝ) ∧
    (delq D.host : ℝ) / (Nat.card (levelU D.host) : ℝ) ≤ 1

def ClaimUnipValuation : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (_ : ParameterChoice' D L) (l : ℕ), l.Prime →
    padicValNat l (Nat.card (levelU D.host)) =
      if l = D.host.g 0 ∨ l = D.host.g 1 then D.R.f * (D.R.r * (D.R.r - 1) / 2) else 0

def ClaimRegularType : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [CharZero K] (r : ℕ) (s : SSParam p K r), IsRegularParam s →
    IsIrrCharacter (typeChar s) ∧
    ∀ s' : SSParam p K r, IsRegularParam s' →
      (typeChar s = typeChar s' ↔ Set.range (rootChar s) = Set.range (rootChar s'))

def ClaimIdempotent : Prop :=
  ∀ (R : Ranks) (H : Host R) (K : Type) [Field K] [NumberField K] (om : ∀ i : Fin 2, (ZMod (H.g i))ˣ →* Kˣ),
    HasLevelRoots H K → IsGeneratorFamily om →
    (∀ τ ∈ goodTypes om, IsIrrCharacter τ) ∧
    IsIdempotentElem (goodIdem om) ∧ goodIdem om ∈ Subalgebra.center K (MonoidAlgebra K (LevelGroup H)) ∧
    (∀ a, IsIntegral ℤ ((Nat.card (LevelGroup H) : K) * (goodIdem om).coeff a)) ∧
    (∀ a, (goodIdem om).coeff a ∈ Subfield.closure {y : K | ∃ i j x, y = ((chiTame om i j x : Kˣ) : K)}) ∧
    ∀ j, IsIdempotentElem (goodIdemTw om j) ∧
      goodIdemTw om j ∈ Subalgebra.center K (MonoidAlgebra K (LevelGroup H)) ∧
      goodIdemTw om j =
        ∑ τ ∈ (goodTypes_finite om).toFinset, centralIdem (fun a => τ a * ((chiDet om j a : Kˣ) : K))

def ClaimLeaves : Prop :=
  ∀ (D : D7) (L : SizeData₂ D) (_ : ParameterChoice' D L) (K : Type) [Field K] [NumberField K] [StarRing K]
    (Bs : DefBase K) (Df : DefSide Bs) (S : IndefData Df) (c : OnConst)
    (ψ : ∀ v : Sq D.host, AddChar (ZMod (D.host.g v.1)) (𝓞 K)) (om : ∀ i : Fin 2, (ZMod (D.host.g i))ˣ →* Kˣ)
    (jx : Bs.J ≃ Fin D.R.m) (O : OnObj S (levelP D.host) c)
    (ρ₀ : ∀ j, Representation K (LevelGroup D.host) (Fin (O.nZ j) → K)),
    LevelTie L ψ om jx O ρ₀ →
      LeafMackey O ∧ LeafIndexU O ∧ LeafUnip O ∧ LeafProj O ∧
      ∀ j (h : levelP D.host), O.e j ∘ₗ O.ρ j h = O.ρ j h ∘ₗ O.e j

end GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters
