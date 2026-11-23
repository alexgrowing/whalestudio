import Development.EtaleCohomology.KummerTheory.InjSlice

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.KummerTheory.LHCut

abbrev SlShv (Λ : Type) [CommRing Λ] (S : Scheme.{0}) : Type 2 :=
  Sheaf (Scheme.etaleTopology.over S) (ModuleCat.{1} (ULift.{1} Λ))

instance (Λ : Type) [CommRing Λ] (S : Scheme.{0}) : HasSheafify (Scheme.etaleTopology.over S) (ModuleCat.{1} (ULift.{1} Λ)) := by
  have : EssentiallySmall.{1} (Over S) := inferInstance
  infer_instance

instance (Λ : Type) [CommRing Λ] (S : Scheme.{0}) : IsGrothendieckAbelian.{1} (SlShv Λ S) := by
  have : EssentiallySmall.{1} (Over S) := inferInstance
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall _ (ModuleCat.{1} (ULift.{1} Λ))

def rst {X S : Scheme.{0}} (p : X ⟶ S) {V U : Over S} (g : V ⟶ U) : pullback p V.hom ⟶ pullback p U.hom :=
  pullback.map _ _ _ _ (𝟙 X) g.left (𝟙 S) (by simp) (by simp)

def Nbhd {S : Scheme.{0}} {V U : Over S} (g : V ⟶ U) (u : U.left) : Prop := Etale g.left ∧ ∃ v : V.left, g.left v = u

section Cone
variable {Λ : Type} [CommRing Λ] {I : Cx Λ} {X S : Scheme.{0}}

abbrev FinalTheorems (J : Cx Λ) (r : ℕ → ℕ) (M : ℕ) (n : ℤ) (U : Scheme.{0}) : Type 1 :=
  ∀ a : Fin (M + 1), Fin (r a) → Sec (J.X (n - ((a : ℕ) : ℤ))) U

abbrev Cone (J K : Cx Λ) (p : X ⟶ S) (r : ℕ → ℕ) (M : ℕ) (j : ℤ) (U : Over S) : Type 1 :=
  FinalTheorems J r M (j + 1) U.left × Sec (K.X j) (pullback p U.hom)

variable {J K : Cx Λ} {r : ℕ → ℕ} {M : ℕ}

def dS (n m : ℤ) {U : Scheme.{0}} (b : FinalTheorems J r M n U) : FinalTheorems J r M m U :=
  fun a s => ((a : ℕ) : ℤ).negOnePow • Sec.map (J.d (n - ((a : ℕ) : ℤ)) (m - ((a : ℕ) : ℤ))) (b a s)

def cres {p : X ⟶ S} {j : ℤ} {V U : Over S} (g : V ⟶ U) (x : Cone J K p r M j U) : Cone J K p r M j V :=
  (fun a s => Sec.res g.left (x.1 a s), Sec.res (rst p g) x.2)

variable (μ : Pair I J K) (p : X ⟶ S) (γ : ∀ a : ℕ, Fin (r a) → Sec (I.X (a : ℤ)) X)

def Phi (n w : ℤ) (h : n = w) (U : Over S) (b : FinalTheorems J r M n U.left) : Sec (K.X w) (pullback p U.hom) :=
  ∑ a : Fin (M + 1), ∑ s : Fin (r a), μ.mul _ ((a : ℕ) : ℤ) (n - ((a : ℕ) : ℤ)) w (by omega)
    (Sec.res (pullback.fst p U.hom) (γ a s)) (Sec.res (pullback.snd p U.hom) (b a s))

def cD (j j' : ℤ) (h : j + 1 = j') (U : Over S) (x : Cone J K p r M j U) : Cone J K p r M j' U :=
  (dS (j + 1) (j' + 1) x.1, Phi μ p γ (j + 1) j' h U x.1 - Sec.map (K.d j j') x.2)

variable (M)

def ConeEx (N : ℕ) (j : ℤ) (U : Over S) : Prop := ∀ x : Cone J K p r M j U, cD μ p γ j (j + 1) rfl U x = 0 →
  ∃ y : Cone J K p r M (j - 1) U, cD μ p γ (j - 1) j (by omega) U y = N • x

def ConeLoc (N : ℕ) (j : ℤ) : Prop := ∀ (U : Over S) (x : Cone J K p r M j U), cD μ p γ j (j + 1) rfl U x = 0 →
  ∀ u : U.left, ∃ (V : Over S) (g : V ⟶ U), Nbhd g u ∧
    ∃ y : Cone J K p r M (j - 1) V, cD μ p γ (j - 1) j (by omega) V y = N • cres g x

end Cone

def Closed {Λ : Type} [CommRing Λ] {I : Cx Λ} {X : Scheme.{0}} {r : ℕ → ℕ} (γ : ∀ a : ℕ, Fin (r a) → Sec (I.X (a : ℤ)) X) : Prop :=
  ∀ (a : ℕ) (s : Fin (r a)), Sec.map (I.d a (a + 1)) (γ a s) = 0

def InjPos {Λ : Type} [CommRing Λ] (J : Cx Λ) : Prop := (∀ n, Injective (J.X n)) ∧ ∀ n : ℤ, n < 0 → IsZero (J.X n)

def mu (q : ℕ) (i : ℤ) : Pair (res _ (tw q i)) (res _ (tw q 0)) (res _ (tw q i)) :=
  cast (congrArg (fun w => Pair (res _ (tw q i)) (res _ (tw q 0)) (res _ (tw q w))) (add_zero i)) (twPair q i 0)

section Cls
variable (q : ℕ) {X S : Scheme.{0}} (p : X ⟶ S) (i : ℤ) (r : ℕ → ℕ) (c : ∀ a : ℕ, Fin (r a) → Ht q (sch.obj X) a i) (M N : ℕ) (n : ℤ)

def KerLoc : Prop := ∀ (U : Over S) (u : U.left) y, lh q p U.hom i r c M n y = 0 →
  ∃ (V : Over S) (g : V ⟶ U), Nbhd g u ∧ ∀ a s, N • pull _ (sch.map g.left) _ _ (y a s) = 0

def CokLoc : Prop := ∀ (U : Over S) (u : U.left) (x : Ht q (sch.obj (pullback p U.hom)) n i),
  ∃ (V : Over S) (g : V ⟶ U), Nbhd g u ∧ ∃ y, lh q p V.hom i r c M n y = N • pull _ (sch.map (rst p g)) _ _ x

end Cls

def ClsMore : Prop := ∀ (Λ : Type) [CommRing Λ] (I : Cx Λ) (X : Scheme.{0}) (n : ℤ),
  IsCls (0 : CohomologyClass ((chains Λ).obj (sch.obj X)) I n) 0 ∧
  (∀ (N : ℕ) x (a : Sec (I.X n) X), IsCls x a → IsCls (N • x) (N • a)) ∧
  (∀ (ι : Type) [Fintype ι] (x : ι → CohomologyClass ((chains Λ).obj (sch.obj X)) I n) (a : ι → Sec (I.X n) X),
    (∀ t, IsCls (x t) (a t)) → IsCls (∑ t, x t) (∑ t, a t)) ∧
  ∀ (m : ℤ), m + 1 = n → ∀ x x' (a a' : Sec (I.X n) X), IsCls x a → IsCls x' a' →
    (x = x' ↔ ∃ b : Sec (I.X m) X, Sec.map (I.d m n) b = a - a')

def LhSec : Prop := ∀ (q : ℕ) {X S : Scheme.{0}} (p : X ⟶ S) (i : ℤ) (r : ℕ → ℕ) (c : ∀ a : ℕ, Fin (r a) → Ht q (sch.obj X) a i)
  (γ : ∀ a : ℕ, Fin (r a) → Sec ((res _ (tw q i)).X (a : ℤ)) X), (∀ a s, IsCls (c a s) (γ a s)) →
  ∀ (M : ℕ) (n : ℤ) (U : Over S) y (b : FinalTheorems (res _ (tw q 0)) r M n U.left), (∀ a s, IsCls (y a s) (b a s)) →
  IsCls (lh q p U.hom i r c M n y) (Phi (mu q i) p γ n n rfl U b)

def LhNat : Prop := DivisorNaturality → ∀ (q : ℕ) [NeZero q] {X S : Scheme.{0}} (p : X ⟶ S) (i : ℤ) (r : ℕ → ℕ)
  (c : ∀ a : ℕ, Fin (r a) → Ht q (sch.obj X) a i) (M : ℕ) (n : ℤ) {V U : Over S} (g : V ⟶ U) y,
  pull _ (sch.map (rst p g)) _ _ (lh q p U.hom i r c M n y) =
    lh q p V.hom i r c M n (fun a s => pull _ (sch.map g.left) _ _ (y a s))

def ConeAlg : Prop := ∀ (Λ : Type) [CommRing Λ] {I J K : Cx Λ} (μ : Pair I J K) {X S : Scheme.{0}} (p : X ⟶ S) (r : ℕ → ℕ) (M : ℕ)
  (γ : ∀ a : ℕ, Fin (r a) → Sec (I.X (a : ℤ)) X), Closed γ → ∀ (j j' : ℤ) (h : j + 1 = j') (U : Over S),
  IsLinearMap (ULift.{1} Λ) (cD (M := M) μ p γ j j' h U) ∧
  (∀ (j'' : ℤ) (h' : j' + 1 = j'') (x : Cone J K p r M j U), cD μ p γ j' j'' h' U (cD μ p γ j j' h U x) = 0) ∧
  ∀ (V : Over S) (g : V ⟶ U), IsLinearMap (ULift.{1} Λ) (cres g : Cone J K p r M j U → _) ∧
    (∀ x : Cone J K p r M j U, cres g (cD μ p γ j j' h U x) = cD μ p γ j j' h V (cres g x)) ∧
    ∀ (W : Over S) (g' : W ⟶ V) (x : Cone J K p r M j U), cres (g' ≫ g) x = cres g' (cres g x)

def LocKer : Prop := DivisorNaturality → B1 → ∀ (q : ℕ) [NeZero q] {X : Scheme.{0}} {R : CommRingCat.{0}} (p : X ⟶ Spec R), IsUnit (q : R) →
  ∀ (i : ℤ) (r : ℕ → ℕ) (c : ∀ a : ℕ, Fin (r a) → Ht q (sch.obj X) a i) (M N : ℕ) (n : ℤ),
  (∀ (A : CommRingCat.{0}) (s : R ⟶ A), SH A → IsoUpTo N (lh q p (Spec.map s) i r c M n)) → KerLoc q p i r c M N n

def LocCok : Prop := A2 → DivisorNaturality → B1 → ∀ (q : ℕ) [NeZero q] {X : Scheme.{0}} {R : CommRingCat.{0}} (p : X ⟶ Spec R)
  [QuasiCompact p] [IsSeparated p], IsUnit (q : R) →
  ∀ (i : ℤ) (r : ℕ → ℕ) (c : ∀ a : ℕ, Fin (r a) → Ht q (sch.obj X) a i) (M N : ℕ) (n : ℤ),
  (∀ (A : CommRingCat.{0}) (s : R ⟶ A), SH A → IsoUpTo N (lh q p (Spec.map s) i r c M n)) → CokLoc q p i r c M N n

def LocCone : Prop := ∀ (q : ℕ) {X S : Scheme.{0}} (p : X ⟶ S) (i : ℤ) (r : ℕ → ℕ) (c : ∀ a : ℕ, Fin (r a) → Ht q (sch.obj X) a i)
  (γ : ∀ a : ℕ, Fin (r a) → Sec ((res _ (tw q i)).X (a : ℤ)) X), (∀ a s, IsCls (c a s) (γ a s)) → ∀ (M N : ℕ) (j : ℤ),
  KerLoc q p i r c M N (j + 1) → CokLoc q p i r c M N j → ConeLoc M (mu q i) p γ (N ^ 2) j

def ExIso : Prop := ∀ (q : ℕ) {X S : Scheme.{0}} (p : X ⟶ S) (i : ℤ) (r : ℕ → ℕ) (c : ∀ a : ℕ, Fin (r a) → Ht q (sch.obj X) a i)
  (γ : ∀ a : ℕ, Fin (r a) → Sec ((res _ (tw q i)).X (a : ℤ)) X), (∀ a s, IsCls (c a s) (γ a s)) → ∀ (M N : ℕ) (j : ℤ) (U : Over S),
  ConeEx M (mu q i) p γ N j U → ConeEx M (mu q i) p γ N (j + 1) U → IsoUpTo N (lh q p U.hom i r c M (j + 1))

def Corep : Prop := ∀ (Λ : Type) [CommRing Λ] (S : Scheme.{0}) (U : Over S), ∃ (P : SlShv Λ S) (z : P.obj.obj (op U)),
  ∀ F : SlShv Λ S, Function.Bijective fun φ : P ⟶ F => (φ.hom.app (op U)).hom z

def CxLoc {Λ : Type} [CommRing Λ] {S : Scheme.{0}} (C : CochainComplex (SlShv Λ S) ℤ) (N : ℕ) (j : ℤ) : Prop :=
  ∀ (U : Over S) (x : (C.X j).obj.obj (op U)), ((C.d j (j + 1)).hom.app (op U)).hom x = 0 → ∀ u : U.left,
    ∃ (V : Over S) (g : V ⟶ U), Nbhd g u ∧ ∃ y : (C.X (j - 1)).obj.obj (op V),
      ((C.d (j - 1) j).hom.app (op V)).hom y = N • ((C.X j).obj.map g.op).hom x

def HomKill : Prop := ∀ (Λ : Type) [CommRing Λ] (S : Scheme.{0}) (C : CochainComplex (SlShv Λ S) ℤ) (N : ℕ) (j : ℤ),
  CxLoc C N j → N • 𝟙 (C.homology j) = 0

def GhostSec : Prop := ∀ (Λ : Type) [CommRing Λ] (S : Scheme.{0}) (C : CochainComplex (SlShv Λ S) ℤ), (∀ j, Injective (C.X j)) →
  (∀ j : ℤ, j < -1 → IsZero (C.X j)) → ∀ N m : ℕ, (∀ j : ℤ, j < m → CxLoc C N j) → ∀ j : ℤ, j < m →
  ∀ (U : Over S) (x : (C.X j).obj.obj (op U)), ((C.d j (j + 1)).hom.app (op U)).hom x = 0 →
    ∃ y : (C.X (j - 1)).obj.obj (op U), ((C.d (j - 1) j).hom.app (op U)).hom y = N ^ (m + 1) • x

def ConeObj : Prop := ∀ (Λ : Type) [CommRing Λ] (J K : Cx Λ), (∀ n, Injective (J.X n)) → (∀ n, Injective (K.X n)) →
  ∀ {X S : Scheme.{0}} (p : X ⟶ S) (r : ℕ → ℕ) (M : ℕ) (j : ℤ), ∃ T : SlShv Λ S, Injective T ∧
    ∃ e : ∀ U : Over S, T.obj.obj (op U) ≃ₗ[ULift.{1} Λ] Cone J K p r M j U,
      ∀ (V U : Over S) (g : V ⟶ U) x, e V ((T.obj.map g.op).hom x) = cres g (e U x)

def ConeCx : Prop := ∀ (Λ : Type) [CommRing Λ] {I J K : Cx Λ} (μ : Pair I J K), InjPos J → InjPos K →
  ∀ {X S : Scheme.{0}} (p : X ⟶ S) (r : ℕ → ℕ) (M : ℕ) (γ : ∀ a : ℕ, Fin (r a) → Sec (I.X (a : ℤ)) X), Closed γ →
  ∃ C : CochainComplex (SlShv Λ S) ℤ, (∀ j, Injective (C.X j)) ∧ (∀ j : ℤ, j < -1 → IsZero (C.X j)) ∧
    ∃ e : ∀ (j : ℤ) (U : Over S), (C.X j).obj.obj (op U) ≃+ Cone J K p r M j U,
      (∀ (j : ℤ) (V U : Over S) (g : V ⟶ U) x, e j V (((C.X j).obj.map g.op).hom x) = cres g (e j U x)) ∧
      ∀ (j j' : ℤ) (h : j + 1 = j') (U : Over S) x, e j' U (((C.d j j').hom.app (op U)).hom x) = cD μ p γ j j' h U (e j U x)

def Glob : Prop := ∀ (Λ : Type) [CommRing Λ] {I J K : Cx Λ} (μ : Pair I J K), InjPos J → InjPos K →
  ∀ {X S : Scheme.{0}} (p : X ⟶ S) (r : ℕ → ℕ) (M : ℕ) (γ : ∀ a : ℕ, Fin (r a) → Sec (I.X (a : ℤ)) X), Closed γ →
  ∀ N m : ℕ, (∀ j : ℤ, j < m → ConeLoc M μ p γ N j) → ∀ j : ℤ, j < m → ∀ U : Over S, ConeEx M μ p γ (N ^ (m + 1)) j U

theorem injPos_res (Λ : Type) [CommRing Λ] (F : Shv Λ) : InjPos (res Λ F) :=
  ⟨fun n => by unfold res; infer_instance,
   fun n hn => (injectiveResolution F).cochainComplex.isZero_of_isStrictlyGE 0 n hn⟩

theorem goal_of (hD : Dict) (h1 : LocKer) (h2 : LocCok) (h3 : LocCone) (h4 : Glob) (h5 : ExIso) : LH := by
  intro a2 a6 b1
  refine ⟨fun M => 2 * (M + 1), ?_⟩
  intro q _ X R p _ _ hq i r c M N hS Y pY n hn
  choose γ hγ using fun (a : ℕ) (s : Fin (r a)) => (hD _ (res _ (tw q i)) X a).2.1 (c a s)
  have hc : Closed γ := fun a s => ((hD _ (res _ (tw q i)) X a).2.2.1 _ _ (hγ a s)).1
  have hl : ∀ j : ℤ, j < M → ConeLoc M (mu q i) p γ (N ^ 2) j := fun j hj =>
    h3 q p i r c γ hγ M N j (h1 a6 b1 q p hq i r c M N _ fun A s hA => hS A s hA _ (by omega))
      (h2 a2 a6 b1 q p hq i r c M N _ fun A s hA => hS A s hA _ (by omega))
  have hg := h4 _ (mu q i) (injPos_res _ _) (injPos_res _ _) p r M γ hc (N ^ 2) M hl
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  have := h5 q p i r c γ hγ M _ j (Over.mk pY) (hg j (by omega) _) (hg (j + 1) hn _)
  rw [← pow_mul] at this
  exact this

end LateralTheory.KummerTheory.LHCut

end
