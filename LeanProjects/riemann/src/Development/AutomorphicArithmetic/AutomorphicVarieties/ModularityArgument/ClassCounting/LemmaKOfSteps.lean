import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.HasVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.TorsBoundPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.Formula

noncomputable section

open NumberField NumberField.InfinitePlace IsDedekindDomain UpperTheory.V.KL Formalism.GaloisCohomology Polynomial

namespace UpperTheory.V.ZK

def BOdd : Prop :=
  ∀ (L : Type) [Field L] [NumberField L], IsTotallyComplex L → ∀ k : ℕ, Even k → k + 1 < nrComplexPlaces L →
    ∀ (l : ℕ) (hl : 0 < l) (n : ℕ), 2 * (k + 1) + 4 ≤ n →
      Module.rank ℤ (Submodule.span ℤ (Set.range fun x : grpH (GL (Fin n) (𝓞 L)) (k + 1) => zSeq (𝓞 L) hl x k)) ≤
        nrComplexPlaces L

def SChain : Prop :=
  ∀ (A : Type) [CommRing A],
    (∀ (G : Type) [Group G] (m : ℕ) (z : Ch A G (m + 2)), bd A G m (bd A G (m + 1) z) = 0) ∧
    (∀ (G H : Type) [Group G] [Group H] (f : G →* H) (m : ℕ) (z : Ch A G (m + 1)),
      bd A H m (cm A f (m + 1) z) = cm A f m (bd A G m z)) ∧
    (∀ (G H K : Type) [Group G] [Group H] [Group K] (f : G →* H) (g : H →* K) (m : ℕ) (z : Ch A G m),
      cm A (g.comp f) m z = cm A g m (cm A f m z)) ∧
    (∀ (G H : Type) [Group G] [Group H] (f : G →* H) (k : G) (m : ℕ) (z : Ch A G m),
      cm A f (m + 1) (prism A k m z) = prism A (f k) m (cm A f m z)) ∧
    ∀ (G : Type) [Group G] [Subsingleton G] (m : ℕ) (z : Ch A G (m + 1)), Cyc z → Bd z

def SPrism : Prop :=
  ∀ (A : Type) [CommRing A] (G : Type) [Group G] (k : G) (m : ℕ) (z : Ch A G (m + 1)),
    bd A G (m + 1) (prism A k (m + 1) z) + prism A k m (bd A G m z) =
      cm A (MulAut.conj k⁻¹).toMonoidHom (m + 1) z - z

def SPrismMul : Prop :=
  ∀ (A : Type) [CommRing A] (G : Type) [Group G] (k k' : G) (m : ℕ) (z : Ch A G (m + 1)), Cyc z →
    Bd (prism A (k * k') (m + 1) z - prism A k (m + 1) z -
      prism A k' (m + 1) (cm A (MulAut.conj k⁻¹).toMonoidHom (m + 1) z))

def SZc : Prop := ∀ (q : ℕ) [NeZero q] (e : ℕ), Cyc (zc q e)

def SRel : Prop :=
  ∀ (l ν e : ℕ) [Fact l.Prime], ∃ (n : Fin (2 * e + 4) → ZMod (l ^ ν)) (t₀ : Fin (2 * e + 4)), IsUnit (n t₀) ∧
    Bd (∑ t, n t • cm (ZMod (l ^ ν)) (dt (l ^ ν) t) _ (zc (l ^ ν) e))

def STrans : Prop :=
  ∀ (k : Type) [Field k] [Finite k] (A : Type) [CommRing A], ((Nat.card k : A) = 1) → ∀ (m : ℕ)
    (t : Ch A kˣ (m + 1) →ₗ[A] A), (∀ z, Bd z → t z = 0) →
      ∃ θ : Fam k A (m + 1), IsAdd θ ∧ ∀ z : Ch A kˣ (m + 1), Cyc z → θ k (cm A (scal k) (m + 1) z) = t z

def SCoc : Prop :=
  ∀ (k : Type) [Field k] [Finite k] (q : ℕ) [NeZero q] (e : ℕ) (ζ : kˣ) (hζ : IsPrimitiveRoot ζ q) (v : kˣ →* Cq q),
    ∃ t : Ch (ZMod q) kˣ (2 * e + 1 + 1 + 1) →ₗ[ZMod q] ZMod q, (∀ z, Bd z → t z = 0) ∧ ∀ (x : ℕ) (g : kˣ),
      t (prism (ZMod q) g _ (cm (ZMod q) (chi q ζ hζ.pow_eq_one x) _ (zc q e))) =
        (x : ZMod q) ^ (e + 1) * Multiplicative.toAdd (v g)

def STheta : Prop :=
  ∀ (k : Type) [Field k] [Finite k] (q : ℕ) [NeZero q] (e : ℕ) (ζ : kˣ) (hζ : IsPrimitiveRoot ζ q) (v : kˣ →* Cq q),
    ∃ θ : Fam k (ZMod q) (2 * e + 1 + 1 + 1), IsAdd θ ∧ HasVal q e ζ hζ.pow_eq_one v θ

def SThetaOf : Prop := SChain → SPrism → SPrismMul → SZc → STrans → SCoc → STheta

structure IsPrimFam {R A B : Type} [CommRing R] [CommRing A] [AddCommGroup B] [Module A B] {m : ℕ}
    (Φ : ∀ n : ℕ, Ch A (GL (Fin n) R) (m + 1) →ₗ[A] B) : Prop where
  bdry : ∀ n z, Bd z → Φ n z = 0
  stab : ∀ n n' (h : n ≤ n') z, Cyc z → Φ n' (cm A (stab R n n' h) (m + 1) z) = Φ n z
  psi : ∀ d n z, Cyc z → Φ (d * n) (cm A (psi R d n) (m + 1) z) = (d : A) • Φ n z

def SPhi : Prop :=
  ∀ (k : Type) [Field k] [Finite k] (A : Type) [CommRing A] (m : ℕ) (θ : Fam k A (m + 1)), IsAdd θ →
    ∀ (R : Type) [CommRing R] (r : R →+* k), IsPrimFam fun n => (θ (Fin n → k)).comp (cm A (red r n) (m + 1))

def SEta : Prop :=
  ∀ (l c ν M : ℕ) [Fact l.Prime], M < l ^ c → c ≤ ν → ∀ t₀ : Fin (M + 1), ∃ η : ZMod (l ^ ν) × ZMod (l ^ ν) →₀ ℤ,
    (∀ t : Fin (M + 1), t ≠ t₀ → η.mapDomain (fun x => x.1 + ((t : ℕ) : ZMod (l ^ ν)) * x.2) = 0) ∧
    η.mapDomain (fun x => x.1 + ((t₀ : ℕ) : ZMod (l ^ ν)) * x.2) = ∑ i ∈ Finset.range (M + 1),
      Finsupp.single ((1 + (l : ZMod (l ^ ν)) ^ c) ^ i)
        ((∏ j ∈ Finset.range M, (X - C ((1 + (l : ℤ) ^ c) ^ j)) : ℤ[X]).coeff i)

def SStein : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (J : Type) [Fintype J] (𝔞 𝔟 : J → HeightOneSpectrum (𝓞 F) →₀ ℤ) (β : Fˣ),
    (Nonempty J ∨ β = 1) → (∀ P, ordP P β = ∑ j, (𝔟 j P - 𝔞 j P)) →
      ∃ g : (J → F) ≃ₗ[F] (J → F), LinearEquiv.det g = β ∧ ∀ x : J → F,
        (∀ j P, P.valuation F (x j) ≤ WithZero.exp (-𝔞 j P)) ↔ ∀ j P, P.valuation F (g x j) ≤ WithZero.exp (-𝔟 j P)

def SClass : Prop :=
  ∀ (L F : Type) [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F] (l c ν e : ℕ) [Fact l.Prime]
    (ζ : (𝓞 F)ˣ) (γ : F ≃ₐ[L] F) (h : Lay l c ν ζ γ), 2 * e + 3 < l ^ c →
    ∀ (α : Fˣ) (𝔡 : HeightOneSpectrum (𝓞 F) →₀ ℤ), DivDel γ ((1 + l ^ c) ^ (e + 1)) α 𝔡 →
      ∃ (N : ℕ) (y : Ch (ZMod (l ^ ν)) (GL (Fin N) (𝓞 L)) (2 * e + 1 + 1 + 1)) (b : 𝓞 F), Cyc y ∧ b ≠ 0 ∧
        ∀ (k : Type) [Field k] [Finite k] (r : 𝓞 F →+* k), Function.Surjective (r.comp (algebraMap (𝓞 L) (𝓞 F))) →
          r b ≠ 0 → ∀ (hζ : Units.map (r : 𝓞 F →* k) ζ ^ l ^ ν = 1) (v : kˣ →* Cq (l ^ ν))
            (θ : Fam k (ZMod (l ^ ν)) (2 * e + 1 + 1 + 1)), IsAdd θ → HasVal (l ^ ν) e _ hζ v θ →
            ∃ u : kˣ, Res r (nrm γ ((1 + l ^ c) ^ (e + 1)) α) u ∧
              θ (Fin N → k) (cm _ (red (r.comp (algebraMap (𝓞 L) (𝓞 F))) N) _ y) =
                (pe (1 + l ^ c) (2 * e + 3) (e + 1) : ZMod (l ^ ν)) * Multiplicative.toAdd (v u)

def SClassOf : Prop := SChain → SPrism → SPrismMul → SZc → SRel → SEta → SStein → SClass

def tc (L : Type) [Field L] [NumberField L] (N m : ℕ) : ℕ := Nat.card (K.torsHGL L N m)

def SUpper : Prop :=
  ∀ (L : Type) [Field L] [NumberField L], IsTotallyComplex L → ∀ k : ℕ, Even k → k + 1 < nrComplexPlaces L →
    ∀ (l ν : ℕ) [Fact l.Prime] (B : Type) [AddCommGroup B] [Module (ZMod (l ^ ν)) B]
      (Φ : ∀ n : ℕ, Ch (ZMod (l ^ ν)) (GL (Fin n) (𝓞 L)) (k + 1) →ₗ[ZMod (l ^ ν)] B), IsPrimFam Φ →
      ∀ S : Finset B, (∀ s ∈ S, ∃ n y, Cyc y ∧ s = l ^ k • Φ n y) →
        S.card ≤ (l ^ ν) ^ nrComplexPlaces L * tc L (2 * (k + 1) + 4) (k + 1) * tc L (2 * (k + 1) + 4) k

def SUpperOf : Prop := SChain → BOdd → SUpper

def SDetect : Prop :=
  ∀ (L F : Type) [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F] (l ν : ℕ), l.Prime →
    ∀ ζ : (𝓞 F)ˣ, IsPrimitiveRoot ζ (l ^ ν) → ∀ (β : Fˣ) (b : 𝓞 F), b ≠ 0 →
      (∀ (P : HeightOneSpectrum (𝓞 F)) [P.asIdeal.IsMaximal], b ∉ P.asIdeal →
        Function.Surjective ((Ideal.Quotient.mk P.asIdeal).comp (algebraMap (𝓞 L) (𝓞 F))) →
        letI := Ideal.Quotient.field P.asIdeal
        ∃ s : (𝓞 F ⧸ P.asIdeal)ˣ, Res (Ideal.Quotient.mk P.asIdeal) β (s ^ l ^ ν)) → ∃ δ : Fˣ, β = δ ^ l ^ ν

def Few {L F : Type} [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F] (γ : F ≃ₐ[L] F) (a s q B : ℕ) : Prop :=
  ∀ S : Finset Fˣ, (∀ α ∈ S, ∃ 𝔡, DivDel γ a α 𝔡) →
    (∀ α ∈ S, ∀ α' ∈ S, (∃ δ : Fˣ, nrm γ a α ^ s = nrm γ a α' ^ s * δ ^ q) → α = α') → S.card ≤ B

def gens (L : Type) [Field L] [NumberField L] : ℕ := 2 * Module.finrank ℚ L + Nat.log 2 (classNumber L) + 2

def SCount : Prop :=
  ∀ (L F : Type) [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F], IsTotallyComplex L →
    ∀ (l c ν E b B : ℕ) [Fact l.Prime] (ζ : (𝓞 F)ˣ) (γ : F ≃ₐ[L] F), Lay l c ν ζ γ → 1 ≤ E →
      Few γ ((1 + l ^ c) ^ E) (l ^ b) (l ^ ν) B →
        Finite (EqHom γ ((1 + l ^ c) ^ E) (l ^ ν)) ∧
          Nat.card (EqHom γ ((1 + l ^ c) ^ E) (l ^ ν)) * (l ^ ν) ^ nrComplexPlaces L ≤
            B * l ^ ((b + E.factorization l) * gens L + c + E.factorization l)

def SFew : Prop :=
  ∀ (L F : Type) [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F], IsTotallyComplex L →
    ∀ (l c ν e : ℕ) [Fact l.Prime] (ζ : (𝓞 F)ˣ) (γ : F ≃ₐ[L] F), Lay l c ν ζ γ → 2 * e + 3 < l ^ c →
      2 * e + 3 < nrComplexPlaces L →
        Few γ ((1 + l ^ c) ^ (e + 1)) (l ^ (2 * e + 2 + (2 * e + 3) * (c + (2 * e + 3)))) (l ^ ν)
          ((l ^ ν) ^ nrComplexPlaces L * tc L (4 * e + 10) (2 * e + 3) * tc L (4 * e + 10) (2 * e + 2))

def SFewOf : Prop := STheta → SPhi → SClass → SUpper → SDetect → SFew

def TopRoot (l c : ℕ) (L : Type) [Field L] : Prop :=
  1 ≤ c ∧ (l = 2 → 2 ≤ c) ∧ (∃ z : L, IsPrimitiveRoot z (l ^ c)) ∧ ¬∃ z : L, IsPrimitiveRoot z (l ^ (c + 1))

def SSha : Prop :=
  ∀ (L : Type) [Field L] [NumberField L], IsTotallyComplex L → ∀ (l c E B : ℕ) [Fact l.Prime], TopRoot l c L → 1 ≤ E →
    (∀ (F : Type) [Field F] [NumberField F] [Algebra L F] (ν : ℕ) (ζ : (𝓞 F)ˣ) (γ : F ≃ₐ[L] F), Lay l c ν ζ γ →
      Finite (EqHom γ ((1 + l ^ c) ^ E) (l ^ ν)) ∧ Nat.card (EqHom γ ((1 + l ^ c) ^ E) (l ^ ν)) ≤ B) →
    ∃ s : ℕ, LDataCardLeFinrank.shaInv L l E = s ∧ l ^ s ≤ B

def SLayer : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (l E : ℕ) [Fact l.Prime], HasMuQ l L → 1 ≤ E →
    ∃ (L' : Type) (_ : Field L') (_ : NumberField L') (c d : ℕ), IsTotallyComplex L' ∧ TopRoot l c L' ∧
      2 * E + 1 < l ^ c ∧ 2 * E + 1 < nrComplexPlaces L' ∧ Module.finrank ℚ L' = d * Module.finrank ℚ L ∧
      d ≤ (Module.finrank ℚ L + 1) * (4 * E + 4) ∧ l ^ c ≤ 2 * Module.finrank ℚ L' ∧
      (discr L').natAbs ≤ (discr L).natAbs ^ d * (l ^ c) ^ Module.finrank ℚ L' ∧
      LDataCardLeFinrank.shaInv L l E ≤ LDataCardLeFinrank.shaInv L' l E

def STors : Prop :=
  ∃ C : ℝ, ∀ (L : Type) [Field L] [NumberField L], IsTotallyComplex L → ∀ E : ℕ, 1 ≤ E → ∀ m : ℕ, m ≤ 2 * E + 1 →
    Real.log (tc L (4 * E + 6) m) ≤ kBound C E (Module.finrank ℚ L) (discr L).natAbs

def ShaK (C : ℝ) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L : Type) [Field L] [NumberField L], IsTotallyComplex L → HasMuQ l L → ∀ E : ℕ, 1 ≤ E →
    ∃ s : ℕ, LDataCardLeFinrank.shaInv L l E = s ∧ s * Real.log l ≤ kBound C E (Module.finrank ℚ L) (discr L).natAbs

def SNum : Prop := SFew → SCount → SSha → SLayer → STors → ∃ C, ShaK C

def SFinal : Prop :=
  GlobalTheory.Published.PoitouTateDuality → LocalFinitenessK → LocalTateDualityK → (∃ C, ShaK C) → ∃ CK, LemmaK CK

theorem lemmaK_of_steps (hB : BOdd) (hP : GlobalTheory.Published.PoitouTateDuality) (hF : LocalFinitenessK) (hT : LocalTateDualityK)
    (h1 : SChain) (h2 : SPrism) (h3 : SPrismMul) (h4 : SZc) (h5 : SRel) (h6 : STrans) (h7 : SCoc) (h8 : SThetaOf)
    (h9 : SPhi) (h10 : SEta) (h11 : SStein) (h12 : SClassOf) (h13 : SUpperOf) (h14 : SDetect) (h15 : SCount)
    (h16 : SFewOf) (h17 : SSha) (h18 : SLayer) (h19 : STors) (h20 : SNum) (h21 : SFinal) : ∃ CK, LemmaK CK :=
  h21 hP hF hT (h20 (h16 (h8 h1 h2 h3 h4 h6 h7) h9 (h12 h1 h2 h3 h4 h5 h10 h11) (h13 h1 hB) h14) h15 h17 h18 h19)

end UpperTheory.V.ZK

end
