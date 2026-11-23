import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.DiagApply

noncomputable section

open NumberField IsDedekindDomain Polynomial

namespace UpperTheory.V.ZK.Cl

def CChain : Prop :=
  ∀ (A : Type) [CommRing A] (C D G : Type) [Group C] [Group D] [Group G] (ι : Type) [Fintype ι] (m : ℕ) (H : Subgroup G)
    (ρ : D →* G) (d : ι → C →* D) (n : ι → A) (z : Ch A C (m + 1)) (g : ι → G) (t₀ : ι), Cyc z →
    Bd (∑ t, n t • cm A (d t) (m + 1) z) → (∀ t c, Commute (g t) (ρ (d t c))) → (∀ x, ρ x ∈ H) →
    (∀ x, (g t₀)⁻¹ * ρ x * g t₀ ∈ H) → (∀ t, (g t)⁻¹ * g t₀ ∈ H) →
      ∃ y : Ch A H (m + 2), Cyc y ∧
        Bd (cm A H.subtype (m + 2) y - ∑ t, n t • prism A (g t) (m + 1) (cm A (ρ.comp (d t)) (m + 1) z))

def CFree : Prop :=
  ∀ (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
    (H : Type) [Group H] (α : H →* (M ≃ₗ[R] M)), ∃ (N : ℕ) (lam : H →* GL (Fin N) R),
      ∀ (k : Type) [Field k] (r : R →+* k), Function.Surjective r →
        ∀ (V : Type) [AddCommGroup V] [Module k V] (π : M →+ V) (μ : H →* (V ≃ₗ[k] V)),
          (∀ a x, π (a • x) = r a • π x) → Function.Surjective π →
          (∀ x, π x = 0 → x ∈ RingHom.ker r • (⊤ : Submodule R M)) → (∀ h x, π (α h x) = μ h (π x)) →
            ∃ (P : Submodule k (Fin N → k)) (φ : (V × P) ≃ₗ[k] (Fin N → k)),
              (red r N).comp lam = (cj φ).comp (sumRep μ (1 : H →* (P ≃ₗ[k] P)))

def CTriv : Prop :=
  ∀ (k : Type) [Field k] (A : Type) [CommRing A] (m : ℕ) (θ : Fam k A (m + 1)), IsAdd θ →
    ∀ (H V P U : Type) [Group H] [AddCommGroup V] [Module k V] [Finite V] [AddCommGroup P] [Module k P] [Finite P]
      [AddCommGroup U] [Module k U] [Finite U] (μ : H →* (V ≃ₗ[k] V)) (φ : (V × P) ≃ₗ[k] U) (z : Ch A H (m + 1)), Cyc z →
        θ U (cm A ((cj φ).comp (sumRep μ (1 : H →* (P ≃ₗ[k] P)))) (m + 1) z) = θ V (cm A μ (m + 1) z)

def CBlockVal : Prop :=
  ∀ (k : Type) [Field k] (q : ℕ) [NeZero q] (e : ℕ) (ζ : kˣ) (hζ : ζ ^ q = 1) (v : kˣ →* Cq q)
    (θ : Fam k (ZMod q) (2 * e + 1 + 1 + 1)), IsAdd θ → HasVal q e ζ hζ v θ →
    ∀ (B : Type) [Fintype B] (U : B → Type) [∀ b, AddCommGroup (U b)] [∀ b, Module k (U b)] [∀ b, Finite (U b)]
      (V : Type) [AddCommGroup V] [Module k V] [Finite V] (φ : V ≃ₗ[k] ∀ b, U b) (σ : Cq q →* (V ≃ₗ[k] V))
      (g : V ≃ₗ[k] V) (x : B → ℕ) (g' : ∀ b, U b ≃ₗ[k] U b),
      (∀ c w b, φ (σ c w) b = (chi q ζ hζ (x b) c : k) • φ w b) → (∀ w b, φ (g w) b = g' b (φ w b)) →
        θ V (prism (ZMod q) g _ (cm (ZMod q) σ _ (zc q e))) =
          ∑ b, (x b : ZMod q) ^ (e + 1) * Multiplicative.toAdd (v (LinearEquiv.det (g' b)))

def CAct : Prop :=
  ∀ (L F : Type) [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F],
    (∀ (σ : F ≃ₐ[L] F) (P : HeightOneSpectrum (𝓞 F)) (x : F), (actP σ P).valuation F (σ x) = P.valuation F x) ∧
    (∀ (σ τ : F ≃ₐ[L] F) (P : HeightOneSpectrum (𝓞 F)), actP (σ * τ) P = actP σ (actP τ P)) ∧
    (∀ P : HeightOneSpectrum (𝓞 F), actP (1 : F ≃ₐ[L] F) P = P) ∧
    (∀ (σ : F ≃ₐ[L] F) (P : HeightOneSpectrum (𝓞 F)) (b : 𝓞 L),
      algebraMap (𝓞 L) (𝓞 F) b ∈ (actP σ P).asIdeal ↔ algebraMap (𝓞 L) (𝓞 F) b ∈ P.asIdeal) ∧
    (∀ (σ : F ≃ₐ[L] F) (P : HeightOneSpectrum (𝓞 F)) (α : Fˣ), ordP (actP σ P) (actU σ α) = ordP P α) ∧
    (∀ (P : HeightOneSpectrum (𝓞 F)) (α β : Fˣ), ordP P (α * β) = ordP P α + ordP P β) ∧
    ∀ (P : HeightOneSpectrum (𝓞 F)) (α : Fˣ) (n : ℤ), ordP P (α ^ n) = n * ordP P α

def CRes : Prop :=
  ∀ (L F : Type) [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F] (k : Type) [Field k] (r : 𝓞 F →+* k),
    (∀ x u u', ResF r x u → ResF r x u' → u = u') ∧
    (∀ a : 𝓞 F, ResF r (a : F) (r a)) ∧
    (∀ x y u w, ResF r x u → ResF r y w → ResF r (x + y) (u + w) ∧ ResF r (x * y) (u * w)) ∧
    ∀ b : 𝓞 L, r (algebraMap (𝓞 L) (𝓞 F) b) ≠ 0 →
      (∀ x : F, (∀ P : HeightOneSpectrum (𝓞 F), algebraMap (𝓞 L) (𝓞 F) b ∉ P.asIdeal → P.valuation F x ≤ 1) →
        (∃ (n : ℕ) (a : 𝓞 F), (algebraMap (𝓞 L) F b) ^ n * x = a) ∧ ∃ u, ResF r x u) ∧
      ∀ α : Fˣ, IsBU b α → ∃ u : kˣ, Res r α u

def CSplit : Prop :=
  ∀ (L F : Type) [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F], IsGalois L F → ∃ b : 𝓞 L, b ≠ 0 ∧ ∀ (k : Type) [Field k] [Finite k] (r : 𝓞 F →+* k),
    Function.Surjective (r.comp (algebraMap (𝓞 L) (𝓞 F))) → r (algebraMap (𝓞 L) (𝓞 F) b) ≠ 0 → Split L r

def CSupp : Prop :=
  ∀ (L F : Type) [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F] (𝔡 : HeightOneSpectrum (𝓞 F) →₀ ℤ) (b₀ : 𝓞 L), b₀ ≠ 0 → ∃ b : 𝓞 L, b ≠ 0 ∧ b₀ ∣ b ∧
    ∀ P, 𝔡 P ≠ 0 → algebraMap (𝓞 L) (𝓞 F) b ∈ P.asIdeal

def CLatLoc : Prop :=
  ∀ (L F : Type) [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F] (J : Type) [Fintype J] (b : 𝓞 L), b ≠ 0 → ∀ (𝔞 𝔟 : J → HeightOneSpectrum (𝓞 F) →₀ ℤ),
    (∀ j P, 𝔞 j P ≠ 0 → algebraMap (𝓞 L) (𝓞 F) b ∈ P.asIdeal) →
    (∀ j P, 𝔟 j P ≠ 0 → algebraMap (𝓞 L) (𝓞 F) b ∈ P.asIdeal) →
      ∀ g : GG L F J, (∀ x, InLat 𝔞 x ↔ InLat 𝔟 (g x)) → g ∈ GLoc F J b

def CMu : Prop :=
  ∀ (L F : Type) [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F] (J : Type) [Fintype J] (k : Type) [Field k] (r : 𝓞 F →+* k) (b : 𝓞 L),
    r (algebraMap (𝓞 L) (𝓞 F) b) ≠ 0 → Function.Surjective (r.comp (algebraMap (𝓞 L) (𝓞 F))) → Split L r →
      ∃ μ : GLoc F J b →* (((F ≃ₐ[L] F) × J → k) ≃ₗ[k] ((F ≃ₐ[L] F) × J → k)), IsMu r b μ

def CInt : Prop :=
  ∀ (L F : Type) [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F] (J : Type) [Fintype J] (b : 𝓞 L),
    Module.Finite (𝓞 L) (J → 𝓞 F) ∧ Module.Projective (𝓞 L) (J → 𝓞 F) ∧
    ∃ α : (StabP L (InLat (F := F) (J := J) 0)).subgroupOf (GLoc F J b) →* ((J → 𝓞 F) ≃ₗ[𝓞 L] (J → 𝓞 F)),
      ∀ (k : Type) [Field k] (r : 𝓞 F →+* k), Split L r →
        ∀ μ : GLoc F J b →* (((F ≃ₐ[L] F) × J → k) ≃ₗ[k] ((F ≃ₐ[L] F) × J → k)), IsMu r b μ →
          ∃ π : (J → 𝓞 F) →+ ((F ≃ₐ[L] F) × J → k),
            (∀ (a : 𝓞 L) x, π (a • x) = r.comp (algebraMap (𝓞 L) (𝓞 F)) a • π x) ∧ Function.Surjective π ∧
            (∀ x, π x = 0 → x ∈ RingHom.ker (r.comp (algebraMap (𝓞 L) (𝓞 F))) • (⊤ : Submodule (𝓞 L) (J → 𝓞 F))) ∧
            ∀ h x, π (α h x) = μ h.1 (π x)

def CMat : Prop :=
  ∀ (L F : Type) [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F] (I : Type) [Fintype I] (k : Type) [Field k] (r : 𝓞 F →+* k) (b : 𝓞 L),
    r (algebraMap (𝓞 L) (𝓞 F) b) ≠ 0 → ∀ (g : (I → F) ≃ₗ[F] (I → F)), (∀ x, InLoc b x ↔ InLoc b (g x)) →
      IsBU b (LinearEquiv.det g) ∧ ∀ σ : F ≃ₐ[L] F, ∃ g₁ : (I → k) ≃ₗ[k] (I → k),
        Res r (actU σ (LinearEquiv.det g)) (LinearEquiv.det g₁) ∧
        ∀ (w : I → F) (u : I → k), InLoc b w → (∀ i, ResF r (σ (w i)) (u i)) → ∀ i, ResF r (σ (g w i)) (g₁ u i)

def CBlock : Prop :=
  ∀ (L F : Type) [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F] (J X : Type) (s : J → F ≃ₐ[L] F) (β : J → X)
    (g' : ∀ x : X, ({j // β j = x} → F) ≃ₗ[F] ({j // β j = x} → F)),
    (∃ g : GG L F J, BlockForm g s β g') ∧ ∀ g : GG L F J, BlockForm g s β g' →
      (∀ (u : J → Fˣ) (u' : X → Fˣ), (∀ j, actU (s j) (u j) = u' (β j)) → Commute g (diag L u)) ∧
      (∀ b : 𝓞 L, g ∈ GLoc F J b → ∀ x w, InLoc b w ↔ InLoc b (g' x w)) ∧
      ∀ (𝔟 𝔠 : J → HeightOneSpectrum (𝓞 F) →₀ ℤ), (∀ j P, 𝔠 j (actP (s j) P) = 𝔟 j P) →
        (∀ x w, InLat 0 w ↔ InLat (fun i : {j // β j = x} => 𝔠 i.1) (g' x w)) → ∀ w, InLat 0 w ↔ InLat 𝔟 (g w)

def CVal : Prop :=
  ∀ (L F : Type) [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F] (J : Type) [Fintype J] (q : ℕ) [NeZero q] (e : ℕ) (ζ : (𝓞 F)ˣ) (h : ζ ^ q = 1) (kap : (F ≃ₐ[L] F) → ℕ),
    (∀ σ, actU σ (toF ζ) = toF ζ ^ kap σ) → ∀ (k : Type) [Field k] [Finite k] (r : 𝓞 F →+* k) (b : 𝓞 L),
    r (algebraMap (𝓞 L) (𝓞 F) b) ≠ 0 → Split L r →
    ∀ (μ : GLoc F J b →* (((F ≃ₐ[L] F) × J → k) ≃ₗ[k] ((F ≃ₐ[L] F) × J → k))), IsMu r b μ →
    ∀ (hζ : Units.map (r : 𝓞 F →* k) ζ ^ q = 1) (v : kˣ →* Cq q) (θ : Fam k (ZMod q) (2 * e + 1 + 1 + 1)),
      IsAdd θ → HasVal q e _ hζ v θ → ∀ f : Fˣ → ZMod q, (∀ x u, Res r x u → f x = Multiplicative.toAdd (v u)) →
      ∀ (χ : J → ZMod q) (𝔟 : J → HeightOneSpectrum (𝓞 F) →₀ ℤ) (δ : ZMod q → Fˣ) (g : GLoc F J b) (ρ : Cq q →* GLoc F J b),
        Carries L q ζ χ 𝔟 δ g.1 → (∀ c, (ρ c).1 = repC L q ζ h χ c) →
          θ _ (prism (ZMod q) (μ g) _ (cm (ZMod q) (μ.comp ρ) _ (zc q e))) =
            ∑ σ : F ≃ₐ[L] F, ∑ x : ZMod q, ((kap σ : ZMod q) * x) ^ (e + 1) * f (actU σ (δ x))

def CGtNe : Prop :=
  SStein → ∀ (L F : Type) [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F] (J : Type) [Fintype J] (q : ℕ) [NeZero q] (ζ : (𝓞 F)ˣ) (χ : J → ZMod q) (η : J →₀ ℤ)
    (𝔡 : HeightOneSpectrum (𝓞 F) →₀ ℤ), η.mapDomain χ = 0 → ∃ g : GG L F J, Carries L q ζ χ (fun j => η j • 𝔡) (fun _ => 1) g

def CGtEq : Prop :=
  SStein → ∀ (L F : Type) [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F] (J : Type) [Fintype J] (l c ν M : ℕ) [Fact l.Prime] (ζ : (𝓞 F)ˣ) (γ : F ≃ₐ[L] F), Lay l c ν ζ γ →
    ∀ (χ : J → ZMod (l ^ ν)) (η : J →₀ ℤ) (𝔡 : HeightOneSpectrum (𝓞 F) →₀ ℤ) (p : ℕ → ℤ) (β : Fˣ), (∃ j, χ j = 1) →
      η.mapDomain χ = ∑ i ∈ Finset.range (M + 1), Finsupp.single ((1 + (l : ZMod (l ^ ν)) ^ c) ^ i) (p i) →
      (∀ P, ordP P β = ∑ i ∈ Finset.range (M + 1), p i * 𝔡 (actP (γ ^ i) P)) →
        ∃ g : GG L F J, Carries L (l ^ ν) ζ χ (fun j => η j • 𝔡) (fun x => if x = 1 then β else 1) g

def CBetaDiv : Prop :=
  ∀ (L F : Type) [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F] (γ : F ≃ₐ[L] F) (κ M E : ℕ), E < M → ∀ (α : Fˣ) (𝔡 : HeightOneSpectrum (𝓞 F) →₀ ℤ), DivDel γ (κ ^ E) α 𝔡 →
    ∀ P, ordP P (polAct γ (polE κ M E) α) = ∑ i ∈ Finset.range (M + 1), (pol κ M).coeff i * 𝔡 (actP (γ ^ i) P)

def CBetaVal : Prop :=
  ∀ (L F : Type) [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F] (l c ν E : ℕ) [Fact l.Prime] (ζ : (𝓞 F)ˣ) (γ : F ≃ₐ[L] F), Lay l c ν ζ γ →
    ∀ kap : (F ≃ₐ[L] F) → ℕ, (∀ σ, actU σ (toF ζ) = toF ζ ^ kap σ) → ∀ (U : Subgroup Fˣ) (f : Fˣ → ZMod (l ^ ν)),
      (∀ (σ : F ≃ₐ[L] F), ∀ x ∈ U, actU σ x ∈ U) → (∀ x ∈ U, ∀ y ∈ U, f (x * y) = f x + f y) → ∀ α ∈ U, ∀ p : ℤ[X],
        ∑ σ : F ≃ₐ[L] F, (kap σ : ZMod (l ^ ν)) ^ E * f (actU σ (polAct γ p α)) =
          ((p.eval (((1 + l ^ c) ^ E : ℕ) : ℤ) : ℤ) : ZMod (l ^ ν)) * f (nrm γ ((1 + l ^ c) ^ E) α)

def CRep : Prop :=
  ∀ (L F : Type) [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F] (q : ℕ) [NeZero q] (ζ : (𝓞 F)ˣ) (h : ζ ^ q = 1),
    (∀ (t : ℕ) (c : Cq q), repD L q ζ h (dt q t c) = repC L q ζ h (fun j => j.1 + (t : ZMod q) * j.2) c) ∧
    (∀ (𝔞 : ZMod q × ZMod q → HeightOneSpectrum (𝓞 F) →₀ ℤ) x, repD L q ζ h x ∈ StabP L (InLat 𝔞)) ∧
    (∀ (b : 𝓞 L) x, repD L q ζ h x ∈ GLoc F (ZMod q × ZMod q) b) ∧
    (∀ (J : Type) [Fintype J] (χ : J → ZMod q) (𝔟 : J → HeightOneSpectrum (𝓞 F) →₀ ℤ) (δ : ZMod q → Fˣ) (g : GG L F J),
      Carries L q ζ χ 𝔟 δ g → ∀ c, Commute g (repC L q ζ h χ c)) ∧
    (IsPrimitiveRoot ζ q → ∃ kap : (F ≃ₐ[L] F) → ℕ, ∀ σ, actU σ (toF ζ) = toF ζ ^ kap σ)

def CUnit : Prop :=
  ∀ (L F : Type) [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F] (k : Type) [Field k] (r : 𝓞 F →+* k) (b : 𝓞 L), r (algebraMap (𝓞 L) (𝓞 F) b) ≠ 0 →
    ∀ (q : ℕ) (v : kˣ →* Cq q), ∃ (U : Subgroup Fˣ) (f : Fˣ → ZMod q), (∀ x, x ∈ U ↔ IsBU b x) ∧
      (∀ (σ : F ≃ₐ[L] F), ∀ x ∈ U, actU σ x ∈ U) ∧ (∀ x ∈ U, ∀ y ∈ U, f (x * y) = f x + f y) ∧ f 1 = 0 ∧
      (∀ x u, Res r x u → f x = Multiplicative.toAdd (v u)) ∧ ∀ x ∈ U, ∃ u, Res r x u

def CJoin : Prop :=
  CChain → CFree → CTriv → CAct → CSplit → CSupp → CLatLoc → CMu → CInt → CVal → CGtNe → CGtEq → CBetaDiv → CBetaVal →
    CRep → CUnit → SClassOf

end UpperTheory.V.ZK.Cl

end
