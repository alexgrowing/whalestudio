import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.IsSymb

noncomputable section

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4

namespace UpperTheory.V.Z.Kato.Sym

def LgB : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (m : ℕ), 0 < m → IsPrimitiveRoot (zt X m) m ∧
    (∀ a b : Kb X, b ≠ 0 → a ^ m = b ^ m → a = zt X m ^ (lg X m a b).val * b) ∧
    (∀ (a b : Kb X) (i : ZMod m), b ≠ 0 → a = zt X m ^ i.val * b → lg X m a b = i) ∧
    (∀ a b c : Kb X, c ≠ 0 → a ^ m = b ^ m → b ^ m = c ^ m → lg X m a c = lg X m a b + lg X m b c) ∧
    (∀ a b a' b' : Kb X, b ≠ 0 → b' ≠ 0 → a ^ m = b ^ m → a' ^ m = b' ^ m → lg X m (a * a') (b * b') = lg X m a b + lg X m a' b') ∧
    (∀ (σ : RingAut (Kb X)) (τ : X.K ≃+* X.K) (s : Ω ≃ₐ[ℚ] Ω), admitted X τ s → Lifts X σ τ → ∀ a b : Kb X, b ≠ 0 → a ^ m = b ^ m →
      lg X m (σ a) (σ b) = cyc m s * lg X m a b) ∧
    ∀ s t : Ω ≃ₐ[ℚ] Ω, cyc m (s * t) = cyc m s * cyc m t ∧ cyc m (1 : Ω ≃ₐ[ℚ] Ω) = 1 ∧ ∀ z : Ω, z ^ m = 1 → s z = z ^ (cyc m s).val

def KaB : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (m : ℕ), 0 < m → ∀ (θ : Kb X) (u : X.K), u ≠ 0 → θ ^ m = io X u →
    (∀ g h, InD X g → InD X h → ka X m θ (g * h) = ka X m θ g + ka X m θ h) ∧
    (∀ θ' : Kb X, θ' ^ m = io X u → ∀ h, InD X h → ka X m θ' h = ka X m θ h) ∧ LC X (ka X m θ) ∧
    (IsU X u → Unr X (ka X m θ)) ∧
    (∀ (σ : RingAut (Kb X)) (τ : X.K ≃+* X.K) (s : Ω ≃ₐ[ℚ] Ω), admitted X τ s → Lifts X σ τ → ∀ h, InD X h →
      InD X (σ⁻¹ * h * σ) ∧ ka X m (σ θ) h = cyc m s * ka X m θ (σ⁻¹ * h * σ)) ∧
    ∀ (θ' : Kb X) (u' : X.K), u' ≠ 0 → θ' ^ m = io X u' → ∀ h, InD X h → ka X m (θ * θ') h = ka X m θ h + ka X m θ' h

def AdmB : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), (∀ g : GQ, admitted X (slR X g) 1) ∧ (∀ s, admitted X (X.gal s) s) ∧ admitted X (RingEquiv.refl _) 1 ∧
    (∀ τ s τ' s', admitted X τ s → admitted X τ' s' → admitted X (τ.trans τ') (s' * s)) ∧ (∀ τ s, admitted X τ s → admitted X τ.symm s⁻¹) ∧
    (∀ τ s, admitted X τ s → (∀ u, IsU X u → IsU X (τ u)) ∧ ∀ m f, f ∈ X.Un m → unU X τ f ∈ X.Un m) ∧
    (∀ τ : X.K ≃+* X.K, ∃ σ, Lifts X σ τ) ∧
    ∀ m : ℕ, (1 : X.Kˣ) ∈ X.Un m ∧ ∀ f g, f ∈ X.Un m → g ∈ X.Un m → f * g ∈ X.Un m ∧ f⁻¹ ∈ X.Un m

def Kum : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (m : ℕ), 0 < m → (∀ φ : RingAut (Kb X) → ZMod m,
      (∀ g h, InD X g → InD X h → φ (g * h) = φ g + φ h) → LC X φ → ∃ f, IsKum X m φ f) ∧
    ∀ (φ φ' : RingAut (Kb X) → ZMod m) (f f' : X.Kˣ), IsKum X m φ f → (∀ h, InD X h → φ h = φ' h) → (IsKum X m φ' f' ↔ Cgr m f' f)

def KumUn : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (m : ℕ), 0 < m → ∀ (φ : RingAut (Kb X) → ZMod m) (f : X.Kˣ), IsKum X m φ f → Unr X φ → f ∈ X.Un m

def MvPt : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (m : ℕ), 0 < m → ∀ (τ : X.K ≃+* X.K) (s : Ω ≃ₐ[ℚ] Ω), admitted X τ s → ∀ σ, Lifts X σ τ → ∀ (u v : X.K) (P : Pt X m),
    IsPt X m u v P → IsPt X m (τ u) (τ v) (P.mv σ (cyc m s))

def DifB : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (m : ℕ), 0 < m → ∀ (u v : X.K) (P Q : Pt X m), IsPt X m u v P → IsPt X m u v Q →
    (∀ g h, InD X g → InD X h → dif X P Q (g * h) = dif X P Q g + dif X P Q h) ∧ LC X (dif X P Q) ∧ Unr X (dif X P Q) ∧
    (∀ R, IsPt X m u v R → ∀ h, InD X h → dif X P R h = dif X P Q h + dif X Q R h) ∧ (∀ h, InD X h → dif X P P h = 0) ∧
    (∀ σ, InD X σ → ∀ h, InD X h → dif X (P.mv σ 1) P h = 0) ∧
    ∀ (τ : X.K ≃+* X.K) (s : Ω ≃ₐ[ℚ] Ω), admitted X τ s → ∀ σ, Lifts X σ τ → ∀ h, InD X h →
      dif X (P.mv σ (cyc m s)) (Q.mv σ (cyc m s)) h = cyc m s ^ 2 * dif X P Q (σ⁻¹ * h * σ)

def MvEx : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (m : ℕ), 0 < m → ∀ (τ : X.K ≃+* X.K) (s : Ω ≃ₐ[ℚ] Ω), admitted X τ s → ∀ (u v : X.K) (P : Pt X m), IsPt X m u v P →
    (∀ Q, IsPt X m (τ u) (τ v) Q → ∃ f ∈ X.Un m, Mv X m τ s P Q f) ∧ (∃ Q, IsPt X m (τ u) (τ v) Q ∧ Mv X m τ s P Q 1) ∧
    Mv X m (RingEquiv.refl _) 1 P P 1 ∧
    ∀ Q, IsPt X m (τ u) (τ v) Q → ∀ f f', Mv X m τ s P Q f → (Mv X m τ s P Q f' ↔ Cgr m f' f)

def MvComp : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (m : ℕ), 0 < m → ∀ (τ τ' : X.K ≃+* X.K) (s s' : Ω ≃ₐ[ℚ] Ω), admitted X τ s → admitted X τ' s' →
    ∀ (u v : X.K) (P Q R : Pt X m), IsPt X m u v P → IsPt X m (τ u) (τ v) Q → IsPt X m (τ' (τ u)) (τ' (τ v)) R →
      ∀ f f', Mv X m τ s P Q f → Mv X m τ' s' Q R f' → Mv X m (τ.trans τ') (s' * s) P R (unU X τ' f ^ (cyc m s').val * f')

def MvNear : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (m : ℕ), 0 < m → ∀ (u v : X.K) (P : Pt X m), IsPt X m u v P → ∃ S : Finset X.K,
    ∀ (τ : X.K ≃+* X.K) (s : Ω ≃ₐ[ℚ] Ω), admitted X τ s → (∀ f ∈ S, τ f = f) → Mv X m τ s P P 1

def SumB : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (m : ℕ), 0 < m → ∀ (I J : Type) (A : Finset I) (B : Finset J) (u : I → X.K) (v : J → X.K) (P : I → J → Pt X m),
    A.Nonempty → B.Nonempty → (∀ i ∈ A, ∀ j ∈ B, IsPt X m (u i) (v j) (P i j)) →
    (∃ R, IsSum X m A B P R) ∧ ∀ R, IsSum X m A B P R → IsPt X m (∏ i ∈ A, u i) (∏ j ∈ B, v j) R

def SumMv : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (m : ℕ), 0 < m → ∀ (I J : Type) (A A' : Finset I) (B B' : Finset J) (u u' : I → X.K) (v v' : J → X.K)
    (P P' : I → J → Pt X m) (R R' : Pt X m) (e : I → I) (e' : J → J) (τ : X.K ≃+* X.K) (s : Ω ≃ₐ[ℚ] Ω), admitted X τ s →
    A.Nonempty → B.Nonempty → Set.BijOn e A' A → Set.BijOn e' B' B →
    (∀ i ∈ A, ∀ j ∈ B, IsPt X m (u i) (v j) (P i j)) → (∀ i ∈ A', ∀ j ∈ B', IsPt X m (u' i) (v' j) (P' i j)) →
    (∀ i ∈ A', u' i = τ (u (e i))) → (∀ j ∈ B', v' j = τ (v (e' j))) → IsSum X m A B P R → IsSum X m A' B' P' R' →
    ∀ f : I → J → X.Kˣ, (∀ i ∈ A', ∀ j ∈ B', Mv X m τ s (P (e i) (e' j)) (P' i j) (f i j)) →
      Mv X m τ s R R' (∏ i ∈ A', ∏ j ∈ B', f i j)

def RedB : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (k m : ℕ), 0 < k → 0 < m → (∀ (u v : X.K) (P : Pt X (k * m)), IsPt X (k * m) u v P → IsPt X m u v (P.red k m)) ∧
    ∀ (τ : X.K ≃+* X.K) (s : Ω ≃ₐ[ℚ] Ω), admitted X τ s → ∀ (u v : X.K) (P Q : Pt X (k * m)), IsPt X (k * m) u v P →
      IsPt X (k * m) (τ u) (τ v) Q → ∀ f, Mv X (k * m) τ s P Q f → Mv X m τ s (P.red k m) (Q.red k m) f

def PtEx : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (m : ℕ), 0 < m → ∀ u v : X.K, IsU X u → IsU X v → ∃ P, IsPt X m u v P ∧
    ∀ γ : SL(2, ℤ), X.sl (ofSL γ) u = u → X.sl (ofSL γ) v = v → Mv X m (slR X (ofSL γ)) 1 P P 1

def PtTop : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l n M : ℕ), l.Prime → 0 < M → l ^ n ∣ M → ∀ u v : X.K, IsU X u → IsU X v → u ∈ topF X M → v ∈ topF X M →
    ∃ P, IsPt X (l ^ n) u v P ∧ (∀ γ ∈ CongruenceSubgroup.Gamma M, Mv X (l ^ n) (slR X (ofSL γ)) 1 P P 1) ∧
      ∀ s ∈ fixMu Ω M, ∃ f : X.Kˣ, (f : X.K) = wGen X M l n u v s ∧ Mv X (l ^ n) (X.gal s) s P P f

def SecEx : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (m : ℕ), 0 < m → ∃ t, IsSec X m t

def Recip : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (s : Ω ≃ₐ[ℚ] Ω) (γ : SL(2, ℤ)) (S : Finset X.K), ∃ γ' : SL(2, ℤ), ∀ f ∈ S,
    X.sl (ofSL γ) (X.gal s f) = X.gal s (X.sl (ofSL γ') f)

def GalDg : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (k : ℕ), 0 < k → (∀ (s : Ω ≃ₐ[ℚ] Ω) (f : X.K), X.gal s (X.sl (dg k) f) = X.sl (dg k) (X.gal s f)) ∧
    (∀ γ γ' : SL(2, ℤ), !![(k : ℤ), 0; 0, 1] * (γ : Matrix (Fin 2) (Fin 2) ℤ) = (γ' : Matrix (Fin 2) (Fin 2) ℤ) * !![(k : ℤ), 0; 0, 1] →
      ∀ f, X.sl (ofSL γ) (X.sl (dg k) f) = X.sl (dg k) (X.sl (ofSL γ') f)) ∧
    ∀ M : ℕ, ∀ γ ∈ CongruenceSubgroup.Gamma (k * M), ∃ γ' ∈ CongruenceSubgroup.Gamma M,
      !![(k : ℤ), 0; 0, 1] * (γ : Matrix (Fin 2) (Fin 2) ℤ) = (γ' : Matrix (Fin 2) (Fin 2) ℤ) * !![(k : ℤ), 0; 0, 1]

def SgB : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (c M : ℕ), 1 < c → Nat.Coprime c 6 → 0 < M → Nat.Coprime c M → ∀ x : Row M, x ≠ 0 →
    IsU X (sg X c M x) ∧ (∀ γ : SL(2, ℤ), X.sl (ofSL γ) (sg X c M x) = sg X c M (rt x γ)) ∧
    (∀ s : Ω ≃ₐ[ℚ] Ω, X.gal s (sg X c M x) = sg X c M (gr M s x)) ∧
    ∀ x' : Fin 2 → ℚ, (∀ i, ∃ j : ℤ, x' i = toQ M x i + j) → siegel X c x' = sg X c M x

def RowB : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (M : ℕ), 0 < M →
    (∀ (s t : Ω ≃ₐ[ℚ] Ω) (x : Row M), gr M (s * t) x = gr M s (gr M t x) ∧ gr M (1 : Ω ≃ₐ[ℚ] Ω) x = x) ∧
    (∀ (x y : Row M), Ok x y → x ≠ 0 ∧ y ≠ 0 ∧ (∀ s : Ω ≃ₐ[ℚ] Ω, Ok (gr M s x) (gr M s y)) ∧ ∀ γ : SL(2, ℤ), Ok (rt x γ) (rt y γ)) ∧
    (∀ (γ : SL(2, ℤ)) (x : Row M), γ ∈ CongruenceSubgroup.Gamma M → rt x γ = x) ∧
    ∀ k : ℕ, 0 < k → (∀ x : Row M, toQ (k * M) (up k M x) = toQ M x) ∧
      (∀ x y : Row M, Ok x y → Ok (up k M x) (up k M y)) ∧
      (∀ (s : Ω ≃ₐ[ℚ] Ω) (x : Row M), gr (k * M) s (up k M x) = up k M (gr M s x)) ∧
      (∀ x' y' : Row (k * M), Ok (dn k M x') (dn k M y') → Ok x' y') ∧
      (∀ (s : Ω ≃ₐ[ℚ] Ω) (x' : Row (k * M)), dn k M (gr (k * M) s x') = gr M s (dn k M x')) ∧
      (∀ (γ : SL(2, ℤ)) (x' : Row (k * M)), dn k M (rt x' γ) = rt (dn k M x') γ) ∧ Function.Surjective (dn k M)

def SgDist : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (c k M : ℕ) [NeZero (k * M)], 1 < c → Nat.Coprime c 6 → Nat.Coprime c (k * M) → ∀ x : Row M, x ≠ 0 →
    (open Classical in ∏ x' ∈ Finset.univ.filter (fun x' => dn k M x' = x), sg X c (k * M) x') = sg X c M x

def SgIsog : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (c k M : ℕ) [NeZero (k * M)], 1 < c → Nat.Coprime c 6 → Nat.Coprime c (k * M) → ∀ x : Row M, x ≠ 0 →
    (open Classical in ∏ x' ∈ Finset.univ.filter (fun x' => x' 0 = up k M x 0 ∧ dn k M x' 1 = x 1), sg X c (k * M) x') =
      X.sl (dg k) (sg X c M x)

def PSymb : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (m c d M : ℕ), 0 < m → 1 < c → 1 < d → Nat.Coprime c 6 → Nat.Coprime d 6 → Lv c d M →
    ∀ t, IsSec X m t → ∃ w, IsSymb X m c d M t w

def PCoc : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (m c d M : ℕ), 0 < m → 1 < c → 1 < d → Nat.Coprime c 6 → Nat.Coprime d 6 → Lv c d M →
    ∀ t w, IsSec X m t → IsSymb X m c d M t w → IsCoc X m M w

def Cmp : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (m M : ℕ), 0 < m → 0 < M → ∀ (U V : Row M → X.K) (R Q : Row M → Row M → Pt X m) (F F' : (Ω ≃ₐ[ℚ] Ω) → Fam X M),
    (∀ x y, Ok x y → IsPt X m (U x) (V y) (R x y) ∧ IsPt X m (U x) (V y) (Q x y)) →
    (∀ s x y, Ok x y → X.gal s (U (gr M s⁻¹ x)) = U x ∧ X.gal s (V (gr M s⁻¹ y)) = V y ∧
      Mv X m (X.gal s) s (R (gr M s⁻¹ x) (gr M s⁻¹ y)) (R x y) (F s x y) ∧
      Mv X m (X.gal s) s (Q (gr M s⁻¹ x) (gr M s⁻¹ y)) (Q x y) (F' s x y)) →
    ∃ a : Fam X M, CobBy X m M a F F' ∧ ∀ x y, Ok x y → a x y ∈ X.Un m ∧
      ∀ (τ : X.K ≃+* X.K) (x' y' : Row M), admitted X τ 1 → Ok x' y' → τ (U x) = U x' → τ (V y) = V y' →
        Mv X m τ 1 (R x y) (R x' y') 1 → Mv X m τ 1 (Q x y) (Q x' y') 1 → Cgr m (unU X τ (a x y)) (a x' y')

def PRed : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (k m c d M : ℕ), 0 < k → 0 < m → 1 < c → 1 < d → Nat.Coprime c 6 → Nat.Coprime d 6 → Lv c d M →
    ∀ t' t w' w, IsSec X (k * m) t' → IsSec X m t → IsSymb X (k * m) c d M t' w' → IsSymb X m c d M t w → Coh X m M w' w

def PLev : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (m c d k M : ℕ), 0 < m → 1 < c → 1 < d → Nat.Coprime c 6 → Nat.Coprime d 6 → Lv c d (k * M) →
    ∀ t w' w, IsSec X m t → IsSymb X m c d (k * M) t w' → IsSymb X m c d M t w →
      Coh X m M (fun s x y => w' s (up k M x) (up k M y)) w

def PDist : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (m c d k M : ℕ) [NeZero k] [NeZero M], 0 < m → 1 < c → 1 < d → Nat.Coprime c 6 → Nat.Coprime d 6 → Lv c d (k * M) →
    ∀ t w' w, IsSec X m t → IsSymb X m c d (k * M) t w' → IsSymb X m c d M t w → Coh X m M (fun s => pushD X k M (w' s)) w

def PIsog : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (m c d k M : ℕ) [NeZero k] [NeZero M], 0 < m → 1 < c → 1 < d → Nat.Coprime c 6 → Nat.Coprime d 6 → Lv c d (k * M) →
    ∀ t w' w, IsSec X m t → IsSymb X m c d (k * M) t w' → IsSymb X m c d M t w → ∃ a, EqvH X m k M a ∧
      CobBy X m M a (fun s => pushH X k M (w' s)) fun s x y => slU X (toGQ !![(k : ℤ), 0; 0, 1]) (w s x y)

def PTop : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l n c d k M M' : ℕ), l.Prime → 1 < c → 1 < d → Nat.Coprime c 6 → Nat.Coprime d 6 → Lv c d M → 0 < k → 0 < M' →
    k * M ∣ M' → l ^ n ∣ M' → ∀ t w, IsSec X (l ^ n) t → IsSymb X (l ^ n) c d M t w → ∀ x y : Row M, Ok x y → ∀ x' y' : Fin 2 → ℚ,
    (∀ i, ∃ j : ℤ, x' i = toQ M x i + j) → (∀ i, ∃ j : ℤ, y' i = toQ M y i + j) →
      ∃ a : X.Kˣ, a ∈ X.Un (l ^ n) ∧ (∀ γ ∈ CongruenceSubgroup.Gamma M', Cgr (l ^ n) (slU X (ofSL γ) a) a) ∧ ∀ s ∈ fixMu Ω M', ∃ h : X.Kˣ,
        X.sl (toGQ !![(k : ℤ), 0; 0, 1]) (w s x y : X.K) =
          wGen X M' l n (X.sl (toGQ !![(k : ℤ), 0; 0, 1]) (siegel X c x')) (X.sl (toGQ !![(k : ℤ), 0; 0, 1]) (siegel X d y')) s *
            (X.gal s a / a) * (h : X.K) ^ l ^ n

theorem symEx_of (h1 : SecEx) (h2 : PSymb) (h3 : PCoc) (h4 : PRed) (h5 : PLev) (h6 : PDist) (h7 : PIsog) (h8 : PTop) : SymEx := by
  intro Ω _ _ _ ε X l c d hl hc hd hc6 hd6
  have hpos : ∀ n : ℕ, 0 < l ^ n := fun n => pow_pos hl.pos n
  let t : (n : ℕ) → X.K → X.K → Pt X (l ^ n) := fun n => Classical.choose (h1 Ω ε X (l ^ n) (hpos n))
  have ht : ∀ n, IsSec X (l ^ n) (t n) := fun n => Classical.choose_spec (h1 Ω ε X (l ^ n) (hpos n))
  haveI : ∀ M : ℕ, Nonempty (Gal(Ω/ℚ) → Fam X M) := fun M => ⟨fun _ _ _ => 1⟩
  let w : ℕ → (M : ℕ) → Gal(Ω/ℚ) → Fam X M := fun n M =>
    Classical.epsilon (fun w' => IsSymb X (l ^ n) c d M (t n) w')
  have hw : ∀ n M, Lv c d M → IsSymb X (l ^ n) c d M (t n) (w n M) := fun n M hM =>
    Classical.epsilon_spec (h2 Ω ε X (l ^ n) c d M (hpos n) hc hd hc6 hd6 hM (t n) (ht n))
  have hLv : ∀ k M : ℕ, Lv c d (k * M) → Lv c d M := by
    rintro k M ⟨h0, hcM, hdM⟩
    exact ⟨Nat.pos_of_mul_pos_left h0, Nat.Coprime.coprime_mul_left_right hcM,
      Nat.Coprime.coprime_mul_left_right hdM⟩
  refine ⟨w, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro n M hM
    exact h3 Ω ε X (l ^ n) c d M (hpos n) hc hd hc6 hd6 hM (t n) (w n M) (ht n) (hw n M hM)
  · intro n M hM
    have key : ∀ m' : ℕ, m' = l * l ^ n → ∀ (t' : X.K → X.K → Pt X m') (w' : Gal(Ω/ℚ) → Fam X M),
        IsSec X m' t' → IsSymb X m' c d M t' w' → Coh X (l ^ n) M w' (w n M) := by
      rintro m' rfl t' w' ht' hw'
      exact h4 Ω ε X l (l ^ n) c d M hl.pos (hpos n) hc hd hc6 hd6 hM t' (t n) w' (w n M) ht' (ht n) hw'
        (hw n M hM)
    exact key (l ^ (n + 1)) (pow_succ' l n) (t (n + 1)) (w (n + 1) M) (ht (n + 1)) (hw (n + 1) M hM)
  · intro n k M hkM
    exact h5 Ω ε X (l ^ n) c d k M (hpos n) hc hd hc6 hd6 hkM (t n) (w n (k * M)) (w n M) (ht n)
      (hw n (k * M) hkM) (hw n M (hLv k M hkM))
  · intro n k M _ _ hkM
    exact h6 Ω ε X (l ^ n) c d k M (hpos n) hc hd hc6 hd6 hkM (t n) (w n (k * M)) (w n M) (ht n)
      (hw n (k * M) hkM) (hw n M (hLv k M hkM))
  · intro n k M _ _ hkM
    exact h7 Ω ε X (l ^ n) c d k M (hpos n) hc hd hc6 hd6 hkM (t n) (w n (k * M)) (w n M) (ht n)
      (hw n (k * M) hkM) (hw n M (hLv k M hkM))
  · intro n k M M' hM hk hM' hkM hlM x y hxy x' y' hx' hy'
    exact h8 Ω ε X l n c d k M M' hl hc hd hc6 hd6 hM hk hM' hkM hlM (t n) (w n M) (ht n) (hw n M hM)
      x y hxy x' y' hx' hy'

end UpperTheory.V.Z.Kato.Sym

end
