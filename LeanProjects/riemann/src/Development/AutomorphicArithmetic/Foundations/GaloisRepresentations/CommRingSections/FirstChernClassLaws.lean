import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CommRingSections.IsCovPr

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open GroundTheory.Arith.SchemeCoh

namespace UpperTheory.Gal.DifferentialFormSections

def FmLaws : Prop := ∀ (K : Type) [CommRing K],
  (∀ (A B : Type) [CommRing A] [CommRing B] [Algebra K A] [Algebra K B] (φ : A →ₐ[K] B),
    (∀ a, fmMap φ (algebraMap A _ a) = algebraMap B _ (φ a)) ∧ (∀ a, fmMap φ (dd K a) = dd K (φ a)) ∧
    (∀ n x, fmMap φ (sgn n x) = sgn n (fmMap φ x)) ∧ (∀ (u : Aˣ), fmMap φ (dlog K u) = dlog K (Units.map φ.toMonoidHom u)) ∧
    (∀ (a : ℕ), ∀ x ∈ ⋀[A]^a Ω[A⁄K], fmMap φ x ∈ ⋀[B]^a Ω[B⁄K]) ∧ (Function.Surjective φ → Function.Surjective (fmMap φ)) ∧
    (∀ F G : Fm K A →ₐ[K] Fm K B, (∀ a, F (algebraMap A _ a) = G (algebraMap A _ a)) → (∀ a, F (dd K a) = G (dd K a)) → F = G) ∧
    ∀ (C : Type) [CommRing C] [Algebra K C] (ψ : B →ₐ[K] C) (x : Fm K A), fmMap ψ (fmMap φ x) = fmMap (ψ.comp φ) x) ∧
  (∀ (A : Type) [CommRing A] [Algebra K A], (∀ x : Fm K A, fmMap (AlgHom.id K A) x = x) ∧
    (∀ u v : Aˣ, dlog K (u * v) = dlog K u + dlog K v) ∧ (∀ (n : ℕ) (x y : Fm K A), sgn n (x * y) = sgn n x * sgn n y) ∧
    (∀ (m n : ℕ) (x : Fm K A), sgn m (sgn n x) = sgn (m + n) x) ∧ (∀ x : Fm K A, sgn 0 x = x) ∧ (∀ n, sgn n (1 : Fm K A) = 1) ∧
    ∀ (n a : ℕ), ∀ x ∈ ⋀[A]^a Ω[A⁄K], sgn (K := K) n x = ((-1 : ℤ) ^ (n * a)) • x) ∧
  (∀ (X : Sch K) (U : X.left.Opens) (h : U ≤ U), secRes X h = AlgHom.id K _) ∧
  ∀ {X Y Z : Sch K} (f : Y ⟶ X) (g : Z ⟶ Y) {U : X.left.Opens} {V : Y.left.Opens} {W : Z.left.Opens} (h : V ≤ f.left ⁻¹ᵁ U)
    (h' : W ≤ g.left ⁻¹ᵁ V) (h'' : W ≤ (g ≫ f).left ⁻¹ᵁ U), (secMap g h').comp (secMap f h) = secMap (g ≫ f) h''

def ClsLaws : Prop := ∀ (K : Type) [CommRing K] (X : Sch K) (ι : Type) (U : ι → X.left.Opens) (n : ℕ),
  (∀ σ : Co U n, dC U (n + 1) (dC U n σ) = 0) ∧ (∀ x : HC U n, dC U n (rep x) = 0 ∧ cls (rep x) = x) ∧
  (∀ σ τ : Co U n, dC U n σ = 0 → dC U n τ = 0 → (cls σ = cls τ ↔ σ - τ ∈ Bd U n) ∧ cls (σ + τ) = cls σ + cls τ) ∧
  (∀ (c : K) (σ : Co U n), dC U n σ = 0 → cls (c • σ) = c • cls σ) ∧ cls (0 : Co U n) = 0

def CupCLaws : Prop := ∀ (K : Type) [CommRing K] (X : Sch K) (ι : Type) (U : ι → X.left.Opens) (a b n : ℕ) (h : a + b = n),
  (∀ (σ σ' : Co U a) (τ : Co U b), cupC h (σ + σ') τ = cupC h σ τ + cupC h σ' τ) ∧
  (∀ (σ : Co U a) (τ τ' : Co U b), cupC h σ (τ + τ') = cupC h σ τ + cupC h σ τ') ∧
  (∀ (c : K) (σ : Co U a) (τ : Co U b), cupC h (c • σ) τ = c • cupC h σ τ ∧ cupC h σ (c • τ) = c • cupC h σ τ) ∧
  (∀ (σ : Co U a) (τ : Co U b), dC U n (cupC h σ τ) = cupC (by omega : a + 1 + b = n + 1) (dC U a σ) τ +
    ((-1 : ℤ) ^ a) • cupC (by omega : a + (b + 1) = n + 1) (fun i => sgn 1 (σ i)) (dC U b τ)) ∧
  (∀ σ : Co U a, dC U a (fun i => sgn 1 (σ i)) = fun i => sgn 1 (dC U a σ i)) ∧
  ∀ (c m k : ℕ) (h₁ : n + c = m) (h₂ : b + c = k) (h₃ : a + k = m) (σ : Co U a) (τ : Co U b) (ρ : Co U c),
    cupC h₁ (cupC h σ τ) ρ = cupC h₃ σ (cupC h₂ τ ρ)

def CupLaws : Prop := ∀ (K : Type) [CommRing K] (X : Sch K) (ι : Type) (U : ι → X.left.Opens) (a b n : ℕ) (h : a + b = n),
  (∀ (σ : Co U a) (τ : Co U b), dC U a σ = 0 → dC U b τ = 0 → dC U n (cupC h σ τ) = 0 ∧ cupH h (cls σ) (cls τ) = cls (cupC h σ τ)) ∧
  (∀ (x x' : HC U a) (y : HC U b), cupH h (x + x') y = cupH h x y + cupH h x' y) ∧
  (∀ (x : HC U a) (y y' : HC U b), cupH h x (y + y') = cupH h x y + cupH h x y') ∧
  (∀ (c : K) (x : HC U a) (y : HC U b), cupH h (c • x) y = c • cupH h x y ∧ cupH h x (c • y) = c • cupH h x y) ∧
  (∀ x : HC U a, cupH (zero_add a) (cls fun _ => 1) x = x ∧ cupH (add_zero a) x (cls fun _ => 1) = x) ∧
  (∀ (c m k : ℕ) (h₁ : n + c = m) (h₂ : b + c = k) (h₃ : a + k = m) (x : HC U a) (y : HC U b) (z : HC U c),
    cupH h₁ (cupH h x y) z = cupH h₃ x (cupH h₂ y z)) ∧
  ∀ (r s : ℕ), ∀ x ∈ deg U r a, ∀ y ∈ deg U s b, cupH h x y ∈ deg U (r + s) n

def CupComm : Prop := ∀ (K : Type) [CommRing K] (X : Sch K) (ι : Type) (U : ι → X.left.Opens) (a b n : ℕ) (h : a + b = n)
  (h' : b + a = n) (r s : ℕ), ∀ x ∈ deg U r a, ∀ y ∈ deg U s b, cupH h x y = ((-1 : ℤ) ^ ((r + a) * (s + b))) • cupH h' y x

def PullCLaws : Prop := ∀ (K : Type) [CommRing K] {X Y : Sch K} (f : Y ⟶ X) (ι κ : Type) (U : ι → X.left.Opens) (V : κ → Y.left.Opens)
  (t : κ → ι) (ht : ∀ j, V j ≤ f.left ⁻¹ᵁ U (t j)) (n : ℕ),
  (∀ σ : Co U n, dC V n (pullC f t ht n σ) = pullC f t ht (n + 1) (dC U n σ)) ∧
  (∀ σ : Co U n, dC U n σ = 0 → pullHC f t ht (cls σ) = cls (pullC f t ht n σ)) ∧ IsLinearMap K (pullHC f t ht (n := n)) ∧
  (∀ (a b : ℕ) (h : a + b = n) (x : HC U a) (y : HC U b), pullHC f t ht (cupH h x y) = cupH h (pullHC f t ht x) (pullHC f t ht y)) ∧
  pullHC f t ht (cls (n := 0) fun _ => 1) = cls (fun _ => 1) ∧ (∀ a, ∀ x ∈ deg U a n, pullHC f t ht x ∈ deg V a n) ∧
  ∀ {Z : Sch K} (g : Z ⟶ Y) (μ : Type) (W : μ → Z.left.Opens) (s : μ → κ) (hs : ∀ k, W k ≤ g.left ⁻¹ᵁ V (s k))
    (h : ∀ k, W k ≤ (g ≫ f).left ⁻¹ᵁ U ((t ∘ s) k)) (x : HC U n), pullHC g s hs (pullHC f t ht x) = pullHC (g ≫ f) (t ∘ s) h x

def PullInd : Prop := ∀ (K : Type) [CommRing K] {X Y : Sch K} (f : Y ⟶ X) (ι κ : Type) (U : ι → X.left.Opens) (V : κ → Y.left.Opens)
  (t t' : κ → ι) (ht : ∀ j, V j ≤ f.left ⁻¹ᵁ U (t j)) (ht' : ∀ j, V j ≤ f.left ⁻¹ᵁ U (t' j)) (n : ℕ) (x : HC U n),
  pullHC f t ht x = pullHC f t' ht' x

def AugExact {W : TopCat.{0}} (Q : (Opens W)ᵒᵖ ⥤ AddCommGrpCat.{0}) {κ : Type} (V : κ → Opens W) (T : Opens W) {M : Type} [AddCommGroup M]
    (e : M →+ Q.obj (op T)) : Prop :=
  (∀ m : M, (∀ j, res Q (inf_le_right : V j ⊓ T ≤ T) (e m) = 0) → m = 0) ∧
  (∀ σ : Cochain Q (fun j => V j ⊓ T) 0, d Q _ 0 σ = 0 → ∃ m : M, ∀ i : Fin 1 → κ,
    σ i = res Q ((inter_le (fun j => V j ⊓ T) i 0).trans inf_le_right) (e m)) ∧ CechAcyclic Q fun j => V j ⊓ T

def Master : Prop := ∀ {W X : TopCat.{0}} (f : W ⟶ X) (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{0}) (Q : (Opens W)ᵒᵖ ⥤ AddCommGrpCat.{0})
  (φ : P ⟶ (Opens.map f).op ⋙ Q) (ι κ : Type) (U : ι → Opens X) (V : κ → Opens W) (t : κ → ι)
  (c : ∀ n, Cochain P U n →+ Cochain Q V n),
  (∀ j, V j ≤ (Opens.map f).obj (U (t j))) →
  (∀ n σ (j : Fin (n + 1) → κ) (h : inter V j ≤ (Opens.map f).obj (inter U (t ∘ j))), c n σ j = res Q h (φ.app _ (σ (t ∘ j)))) →
  (∀ n (i : Fin (n + 1) → ι), AugExact Q V ((Opens.map f).obj (inter U i)) (φ.app (op (inter U i))).hom) →
  ∀ n, (∀ σ, d P U n σ = 0 → c n σ ∈ coboundaries Q V n → σ ∈ coboundaries P U n) ∧
    ∀ τ, d Q V n τ = 0 → ∃ σ, d P U n σ = 0 ∧ c n σ - τ ∈ coboundaries Q V n

def QC {X : Scheme.{0}} (P : (Opens X.toTopCat)ᵒᵖ ⥤ AddCommGrpCat.{0}) (S : X.Opens → Prop) : Prop :=
  ∀ T : X.Opens, IsAffineOpen T → S T → ∀ (κ : Type) [Finite κ] (h : κ → Γ(X, T)), (⨆ j, X.basicOpen (h j)) = T →
    AugExact P (fun j => X.basicOpen (h j)) T (AddMonoidHom.id _)

def QCAll : Prop := ∀ {X : Scheme.{0}} [X.IsSeparated] (P : (Opens X.toTopCat)ᵒᵖ ⥤ AddCommGrpCat.{0}) (S : X.Opens → Prop),
  (∀ T T', T' ≤ T → S T → S T') → QC P S → ∀ T : X.Opens, IsAffineOpen T → S T → ∀ (κ : Type) (V : κ → X.Opens),
    (∀ j, IsAffineOpen (V j)) → T ≤ iSup V → AugExact P V T (AddMonoidHom.id _)

def FmQC : Prop := ∀ (K : Type) [CommRing K] (X : Sch K), ∃ (P : (Opens X.left.toTopCat)ᵒᵖ ⥤ AddCommGrpCat.{0})
  (e : ∀ U : X.left.Opens, Fm K (Sec X U) ≃+ P.obj (op U)),
  (∀ (U V : X.left.Opens) (h : V ≤ U) x, e V (fmMap (secRes X h) x) = res P h (e U x)) ∧ QC P fun _ => True

def Ref : Prop := ∀ (K : Type) [CommRing K] (X : Sch K) [X.left.IsSeparated] (ι : Type) (U : ι → X.left.Opens) (hU : IsCov U) (n : ℕ),
  Function.Bijective (down hU (n := n))

def PullLaws : Prop := ∀ (K : Type) [CommRing K] {X Y : Sch K} [Y.left.IsSeparated] (f : Y ⟶ X) (n : ℕ),
  IsLinearMap K (pull f (n := n)) ∧ (∀ (a b : ℕ) (h : a + b = n) (x : H X a) (y : H X b), pull f (cup h x y) = cup h (pull f x) (pull f y)) ∧
  pull f (one X) = one Y ∧
  (∀ (ι κ : Type) (U : ι → X.left.Opens) (V : κ → Y.left.Opens) (hU : IsCov U) (hV : IsCov V) (t : κ → ι)
    (ht : ∀ j, V j ≤ f.left ⁻¹ᵁ U (t j)) (x : H X n), down hV (pull f x) = pullHC f t ht (down hU x)) ∧
  (∀ x : H Y n, pull (𝟙 Y) x = x) ∧ ∀ {Z : Sch K} [Z.left.IsSeparated] (g : Z ⟶ Y) (x : H X n), pull g (pull f x) = pull (g ≫ f) x

def DegLaws : Prop := ∀ (K : Type) [CommRing K] (X : Sch K) (ι : Type) (U : ι → X.left.Opens) (n : ℕ),
  iSupIndep (fun a => deg U a n) ∧ ∀ D : ℕ, (∀ (m : ℕ) (i : Fin (m + 1) → ι) (a : ℕ), D < a →
    ⋀[Sec X (cap U i)]^a Ω[Sec X (cap U i)⁄K] = ⊥) → (⨆ a ∈ Finset.range (D + 1), deg U a n) = ⊤ ∧ ∀ a, D < a → deg U a n = ⊥

def DegPull : Prop := ∀ (K : Type) [CommRing K] {X Y : Sch K} [Y.left.IsSeparated] (a n : ℕ),
  (∀ (κ : Type) (V : κ → Y.left.Opens) (hV : IsCov V) (y : H Y n), y ∈ Hd Y a n ↔ down hV y ∈ deg V a n) ∧
  ∀ f : Y ⟶ X, ∀ x ∈ Hd X a n, pull f x ∈ Hd Y a n

def SmoothTop : Prop := ∀ (K : Type) [CommRing K] (X : Sch K) (D : ℕ) [SmoothOfRelativeDimension D X.hom] (U : X.left.Opens),
  IsAffineOpen U → ∀ a, D < a → ⋀[Sec X U]^a Ω[Sec X U⁄K] = ⊥

def FirstChernClassLaws : Prop := ∀ (K : Type) [CommRing K] {X : Sch K} [X.left.IsSeparated] (L : Coc X),
  dC L.U 1 (fun i => dlog K (L.g i)) = 0 ∧ down L.cov (c1 L) = cls (fun i => dlog K (L.g i)) ∧ c1 L ∈ Hd X 1 1 ∧
  ∀ {Y : Sch K} [Y.left.IsSeparated] (f : Y ⟶ X) (M : Coc Y) (t : M.ι → L.ι) (ht : ∀ j, M.U j ≤ f.left ⁻¹ᵁ L.U (t j)),
    (∀ j, ((M.g j : (Sec Y (cap M.U j))ˣ) : Sec Y (cap M.U j)) = secMap f (cap_le f t ht j) (L.g (t ∘ j)).val) → pull f (c1 L) = c1 M

structure IsDiv {K : Type} [CommRing K] {W E : Sch K} (i : E ⟶ W) (L : Coc W) (s : ∀ j : L.ι, Sec W (L.U j)) : Prop where
  closed : IsClosedImmersion i.left
  ker : ∀ j, RingHom.ker (secMap i (le_refl (i.left ⁻¹ᵁ L.U j))).toRingHom = Ideal.span {s j}
  nzd : ∀ j, s j ∈ nonZeroDivisors (Sec W (L.U j))
  rel : ∀ j : Fin 2 → L.ι, secRes W (inter_le (X := W.left.toTopCat) L.U j 0) (s (j 0)) =
    (L.g j).val * secRes W (inter_le (X := W.left.toTopCat) L.U j 1) (s (j 1))

def H1 : Prop := ∀ (K : Type) [Field K] {W E : Sch K} [W.left.IsSeparated] [Smooth W.hom] (i : E ⟶ W) (L : Coc W)
  (s : ∀ j : L.ι, Sec W (L.U j)), IsDiv i L s → ∀ (n : ℕ) (z : H W n), pull i z = 0 → cup (add_comm 1 n) (c1 L) z = 0

end UpperTheory.Gal.DifferentialFormSections
