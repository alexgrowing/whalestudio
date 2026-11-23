import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConnK
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianPartConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRaynaudTorusWeightFunctionInvariantField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusInvariantLiftAddInvariantCombination
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LogDerivativePrincipalPolarisationIndependent
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatConn

open GlobalTheory.KS.DlogPol (gs_rsT gs_pbT gs_one gs_sub)

section Stalk

variable {X Y Z : Scheme.{0}}

def gsH (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) : Γ(X, U) →+* Z.presheaf.stalk z :=
  (Z.presheaf.germ (r ⁻¹ᵁ U) z h).hom.comp (r.app U).hom

theorem gs_eq_gsH (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) (f : Γ(X, U)) : gs r z U f = gsH r z U h f :=
  gs_eq r z U h f

def cstH {S : Type} [CommRing S] (q : Z ⟶ Sp S) (z : Z) : S →+* Z.presheaf.stalk z :=
  (gsH q z ⊤ trivial).comp (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom

theorem cst_eq_cstH {S : Type} [CommRing S] (q : Z ⟶ Sp S) (z : Z) (a : S) : cst q z a = cstH q z a :=
  gs_eq q z ⊤ trivial _

theorem exists_stalkDer (s : Z ⟶ X) (z : Z) (W₀ : X.Opens) (h₀ : s z ∈ W₀)
    (E : ∀ W : X.Opens, Γ(X, W) → Z.presheaf.stalk z)
    (hadd : ∀ W, W ≤ W₀ → s z ∈ W → ∀ f f', E W (f + f') = E W f + E W f')
    (hmul : ∀ W, W ≤ W₀ → s z ∈ W → ∀ f f', E W (f * f') = gs s z W f * E W f' + gs s z W f' * E W f)
    (hres : ∀ W W' (h : W' ≤ W), W ≤ W₀ → s z ∈ W' → ∀ f, E W' (resG X h f) = E W f) :
    ∃ δ : X.presheaf.stalk (s z) → Z.presheaf.stalk z, (∀ x y, δ (x + y) = δ x + δ y) ∧
      (∀ x y, δ (x * y) = (s.stalkMap z).hom x * δ y + (s.stalkMap z).hom y * δ x) ∧
      ∀ W, W ≤ W₀ → s z ∈ W → ∀ f, δ (gs (𝟙 X) (s z) W f) = E W f := by
  have loc : ∀ W W', W ≤ W₀ → W' ≤ W₀ → s z ∈ W → s z ∈ W' → ∀ f f',
      gs (𝟙 X) (s z) W f = gs (𝟙 X) (s z) W' f' → E W f = E W' f' := by
    intro W W' hW hW' m m' f f' e
    rw [gs_eq (𝟙 X) (s z) W m, gs_eq (𝟙 X) (s z) W' m'] at e
    obtain ⟨U, hU, i, i', e'⟩ := X.presheaf.germ_eq (U := W) (V := W') (s z) m m' f f' e
    rw [← hres W U i.le hW hU, ← hres W' U i'.le hW' hU]
    exact congrArg (E U) e'
  have ex : ∀ x : X.presheaf.stalk (s z), ∃ (W : X.Opens) (f : Γ(X, W)), W ≤ W₀ ∧ s z ∈ W ∧ gs (𝟙 X) (s z) W f = x := by
    intro x
    obtain ⟨U, m, f, e⟩ := X.presheaf.germ_exist x
    refine ⟨U ⊓ W₀, resG X inf_le_left f, inf_le_right, ⟨m, h₀⟩, ?_⟩
    rw [gs_res (𝟙 X) (s z) inf_le_left ⟨m, h₀⟩, gs_eq (𝟙 X) (s z) U m]
    exact e
  have ex₂ : ∀ x y : X.presheaf.stalk (s z), ∃ (W : X.Opens) (f g : Γ(X, W)), W ≤ W₀ ∧ s z ∈ W ∧
      gs (𝟙 X) (s z) W f = x ∧ gs (𝟙 X) (s z) W g = y := by
    intro x y
    obtain ⟨W, f, h₁, m, e⟩ := ex x
    obtain ⟨W', g, -, m', e'⟩ := ex y
    exact ⟨W ⊓ W', resG X inf_le_left f, resG X inf_le_right g, inf_le_left.trans h₁, ⟨m, m'⟩,
      (gs_res (𝟙 X) (s z) inf_le_left ⟨m, m'⟩ _).trans e, (gs_res (𝟙 X) (s z) inf_le_right ⟨m, m'⟩ _).trans e'⟩
  choose U g hU mU eU using ex
  have key : ∀ W, W ≤ W₀ → s z ∈ W → ∀ f, E (U (gs (𝟙 X) (s z) W f)) (g _) = E W f := fun W hW m f =>
    loc _ _ (hU _) hW (mU _) m _ _ (eU _)
  refine ⟨fun x => E (U x) (g x), fun x y => ?_, fun x y => ?_, key⟩
  · obtain ⟨W, f, f', hW, m, rfl, rfl⟩ := ex₂ x y
    beta_reduce
    rw [← gs_add (𝟙 X) (s z) W m, key W hW m, key W hW m, key W hW m, hadd W hW m]
  · obtain ⟨W, f, f', hW, m, rfl, rfl⟩ := ex₂ x y
    beta_reduce
    rw [← gs_mul (𝟙 X) (s z) W m, key W hW m, key W hW m, key W hW m, hmul W hW m, ← gs_stalkMap s z W m,
      ← gs_stalkMap s z W m]

theorem exists_stalkDer_field {W₀ : X.Opens} {d : Fld X} (hd : IsField W₀ d) (a : Z ⟶ X) (z : Z) (h₀ : a z ∈ W₀) :
    ∃ δ : X.presheaf.stalk (a z) → Z.presheaf.stalk z, (∀ x y, δ (x + y) = δ x + δ y) ∧
      (∀ x y, δ (x * y) = (a.stalkMap z).hom x * δ y + (a.stalkMap z).hom y * δ x) ∧
      ∀ W, W ≤ W₀ → a z ∈ W → ∀ f, δ (gs (𝟙 X) (a z) W f) = gs a z W (d W f) :=
  exists_stalkDer a z W₀ h₀ (fun W f => gs a z W (d W f))
    (fun W hW m f f' => by rw [hd.1 W hW, gs_add a z W m])
    (fun W hW m f f' => by rw [hd.2.1 W hW, gs_add a z W m, gs_mul a z W m, gs_mul a z W m])
    (fun W W' h hW m f => by rw [hd.2.2 W W' h hW]; exact gs_res a z h m _)

theorem exists_stalkDer_along {R K : Type} [CommRing R] [Field K] {q : Y ⟶ Sp K} {p : X ⟶ Sp R} {m : Y ⟶ X} {D : R → K}
    {d : ∀ W : X.Opens, Γ(X, W) → Γ(Y, m ⁻¹ᵁ W)} (hd : GlobalTheory.KS.LocDerK q p m D ⊤ d) (b : Z ⟶ Y) (z : Z) :
    ∃ δ : X.presheaf.stalk ((b ≫ m) z) → Z.presheaf.stalk z, (∀ x y, δ (x + y) = δ x + δ y) ∧
      (∀ x y, δ (x * y) = ((b ≫ m).stalkMap z).hom x * δ y + ((b ≫ m).stalkMap z).hom y * δ x) ∧
      ∀ W, (b ≫ m) z ∈ W → ∀ f, δ (gs (𝟙 X) ((b ≫ m) z) W f) = gs b z (m ⁻¹ᵁ W) (d W f) := by
  obtain ⟨δ, h₁, h₂, h₃⟩ := exists_stalkDer (b ≫ m) z ⊤ trivial (fun W f => gs b z (m ⁻¹ᵁ W) (d W f))
    (fun W hW h f f' => by rw [hd.add W hW, gs_add b z (m ⁻¹ᵁ W) h])
    (fun W hW h f f' => by
      rw [hd.mul W hW, gs_add b z (m ⁻¹ᵁ W) h, gs_mul b z (m ⁻¹ᵁ W) h, gs_mul b z (m ⁻¹ᵁ W) h, gs_pull b m z W h,
        gs_pull b m z W h])
    (fun W W' h hW h' f => by
      rw [hd.res W W' h hW]; exact gs_rsT b z (O := m ⁻¹ᵁ W') (fun _ hy => h hy) h' _)
  exact ⟨δ, h₁, h₂, fun W => h₃ W le_top⟩

theorem exists_dlog {A B : Type} [CommRing A] [CommRing B] (π : A →+* B) (δ : A → B)
    (hδ : ∀ x y, δ (x * y) = π x * δ y + π y * δ x) :
    ∃ l : Aˣ →* Multiplicative B, ∀ u : Aˣ, δ u.val = π u.val * (l u).toAdd := by
  refine ⟨MonoidHom.mk' (fun u => Multiplicative.ofAdd (π (u⁻¹).val * δ u.val)) fun u v =>
    (congrArg Multiplicative.ofAdd ?_).trans (ofAdd_add _ _), fun u => ?_⟩
  · have hu : π u.val * π (u⁻¹).val = 1 := by rw [← map_mul, Units.mul_inv, map_one]
    have hv : π v.val * π (v⁻¹).val = 1 := by rw [← map_mul, Units.mul_inv, map_one]
    rw [Units.val_mul, hδ, mul_inv, Units.val_mul, π.map_mul]
    linear_combination (π (v⁻¹).val * δ v.val) * hu + (π (u⁻¹).val * δ u.val) * hv
  · have hu : π u.val * π (u⁻¹).val = 1 := by rw [← map_mul, Units.mul_inv, map_one]
    show δ u.val = π u.val * (π (u⁻¹).val * δ u.val)
    rw [← _root_.mul_assoc, hu, _root_.one_mul]

end Stalk

section General

variable {R : Type} [CommRing R] {G : Over (Sp R)} {n : ℕ} {X : Scheme.{0}} {m : G.left ⟶ X} {L : LB X}
  {dd : Fin n → Fld G.left} {D : R → R} (h : Heat G m L dd D) (ν : R)

def dE (i : h.J) : Fld G.left := fun O f =>
  h.d i O f + constFn G.hom O ν * ∑ a, constFn G.hom O (h.u a) * dd a O f

def pE (i : h.J) : Γ(G.left, h.W i) := h.p i + constFn G.hom (h.W i) ν * h.p' i

theorem isField_dE (hdd : ∀ a, IsField ⊤ (dd a)) (i : h.J) : IsField (h.W i) (dE h ν i) := by
  have h₀ := (h.lift i).1
  refine ⟨fun W hW f f' => ?_, fun W hW f f' => ?_, fun W W' hWW hW f => ?_⟩
  · simp only [dE, h₀.1 W hW, fun a => (hdd a).1 W le_top, mul_add, Finset.sum_add_distrib]
    ring
  · have e : ∑ a, constFn G.hom W (h.u a) * dd a W (f * f') =
        f * ∑ a, constFn G.hom W (h.u a) * dd a W f' + f' * ∑ a, constFn G.hom W (h.u a) * dd a W f := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [(hdd a).2.1 W le_top]; ring
    simp only [dE, h₀.2.1 W hW, e]
    ring
  · simp only [dE, h₀.2.2 W W' hWW hW, fun a => (hdd a).2.2 W W' hWW le_top, map_add, map_sum, map_mul,
      GlobalTheory.KS.GlueDer.res_const]

theorem map_op (e : ℕ) (hν : ν * e = 1) (i : h.J) (O : G.left.Opens) (hO : O ≤ h.W i) {A : Type} [CommRing A]
    (π : Γ(G.left, O) →+* A) (hΘ : ∀ a b, π (constFn G.hom O (h.Θ a b)) = 0) (f : Γ(G.left, O)) :
    π (op G dd h.Θ h.u (h.d i) (h.p i) (h.p' i) e O f) =
      2 * (e : A) * (π (dE h ν i O f) + (e : A) * π (rsT (pE h ν i) O) * π f) := by
  have h1 : π (constFn G.hom O ν) * (e : A) = 1 := by
    have : constFn G.hom O ν * (e : Γ(G.left, O)) = 1 := by
      unfold constFn
      rw [← map_natCast (G.hom.appLE ⊤ O (fun _ _ => trivial)).hom,
        ← map_natCast (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom, ← map_mul, ← map_mul, hν, map_one, map_one]
    simpa using congrArg π this
  simp only [op, dE, pE, GlobalTheory.KS.GlueDer.rsT_eq hO, map_add, map_sub, map_mul, map_sum, hΘ, zero_mul,
    Finset.sum_const_zero, sub_zero, map_ofNat, map_natCast, map_pow, GlobalTheory.KS.GlueDer.res_const]
  linear_combination (-2 * ∑ a, π (constFn G.hom O (h.u a)) * π (dd a O f) -
    2 * (e : A) * π (resG G.left hO (h.p' i)) * π f) * h1

end General

section Ray

variable {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X]
  {oa : Q.OAct O} (Y : Ray oa) {n : ℕ} {dd : Fin n → Fld Y.H.left} {D : R → R} (h : Heat Y.H Y.q.left Q.P.L dd D)
  {K : Type} [Field K]

theorem gtφT_eq (α : Q.X) (k : Fin 4) :
    DegPre.gtφT Q Y.H (Y.Φ Y.H (𝟙 _)).b α k = Y.q.left ≫ Q.famφB α (![1, 2, 0, 3] k) := by
  have := Q.P.isAb.comm
  fin_cases k
  · change (padd Q.P.A (toUnit _ ≫ Q.c α) Y.q).left = Y.q.left ≫ (padd Q.P.A (𝟙 Q.P.A) (toUnit _ ≫ Q.c α)).left
    rw [← Over.comp_left]; congr 1
    change (toUnit _ ≫ Q.c α) * Y.q = Y.q ≫ (𝟙 Q.P.A * (toUnit _ ≫ Q.c α))
    rw [MonObj.comp_mul, Category.comp_id, _root_.mul_comm, ← Category.assoc, comp_toUnit]
  · change (toUnit Y.H ≫ Q.c α).left = Y.q.left ≫ (toUnit Q.P.A ≫ Q.c α).left
    rw [← Over.comp_left, ← Category.assoc, comp_toUnit]
  · exact (Category.comp_id _).symm
  · change (toUnit Y.H ≫ η[Q.P.A]).left = Y.q.left ≫ (toUnit Q.P.A ≫ η[Q.P.A]).left
    rw [← Over.comp_left, ← Category.assoc, comp_toUnit]

abbrev xU (α : Q.X) (t : Fin 4 → Q.P.L.ι) : Y.H.left.Opens :=
  LB.wchart Q.P.L (DegPre.gtφT Q Y.H (Y.Φ Y.H (𝟙 _)).b α) fun k => t (![1, 2, 0, 3] k)

abbrev xc (α : Q.X) (t : Fin 4 → Q.P.L.ι) : Γ(Y.H.left, xU Y α t)ˣ :=
  ((Y.Φ Y.H (𝟙 _)).s α).s fun k => t (![1, 2, 0, 3] k)

structure IsFibre (φ : R →+* K) (e : ℕ) (ν : R) (A₀ : Over (Sp K)) [GrpObj A₀] (m₀ : A₀.left ⟶ Q.P.A.left) : Prop where
  field : ∀ a, IsField ⊤ (dd a)
  const : ∀ a V r, dd a V (constFn Y.H.hom V r) = 0
  wt : ∀ a α V f, IsWt Y α V f → IsWt Y α V (dd a V f)
  basic : IsBasic Y h
  symb : ∀ a b, φ (h.Θ a b) = 0
  inv : ν * e = 1
  pull : IsGrpPullback A₀ Q.P.A (spMap φ) m₀

variable (ν : R) {A₀ : Over (Sp K)} (m₀ : A₀.left ⟶ Q.P.A.left) (V : h.J → Q.P.A.left.Opens)
  (ed : ∀ W : Q.P.A.left.Opens, Γ(Q.P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W)) (pb : ∀ i, Γ(A₀.left, m₀ ⁻¹ᵁ V i))

def IsDesc : Prop :=
  (∀ i, h.W i = Y.q.left ⁻¹ᵁ V i) ∧
  (∀ (Z : Scheme.{0}) (a : Z ⟶ Y.H.left) (b : Z ⟶ A₀.left), a ≫ Y.q.left = b ≫ m₀ → ∀ (z : Z) (i : h.J)
    (U : Q.P.A.left.Opens), U ≤ V i → (b ≫ m₀) z ∈ U → ∀ f : Γ(Q.P.A.left, U),
      gs b z (m₀ ⁻¹ᵁ U) (ed U f) = gs a z (Y.q.left ⁻¹ᵁ U) (dE h ν i _ ((Y.q.left.app U).hom f))) ∧
  ∀ (Z : Scheme.{0}) (a : Z ⟶ Y.H.left) (b : Z ⟶ A₀.left), a ≫ Y.q.left = b ≫ m₀ → ∀ (z : Z) (i : h.J),
    (b ≫ m₀) z ∈ V i → gs b z (m₀ ⁻¹ᵁ V i) (pb i) = gs a z (h.W i) (pE h ν i)

variable (Q) in

def Commutes : Prop :=
  ∀ (α : Q.X) (j : Fin 4) (T : A₀.left ⟶ A₀.left), T ≫ m₀ = m₀ ≫ Q.famφB α j → T ≫ A₀.hom = A₀.hom →
    ∀ (W : Q.P.A.left.Opens) (f : Γ(Q.P.A.left, W)) (Z : Scheme.{0}) (b : Z ⟶ A₀.left) (z : Z),
      (b ≫ T ≫ m₀) z ∈ W →
      gs b z (m₀ ⁻¹ᵁ (Q.famφB α j ⁻¹ᵁ W)) (ed _ (((Q.famφB α j).app W).hom f)) = gs (b ≫ T) z (m₀ ⁻¹ᵁ W) (ed W f)

def CoordAt (α : Q.X) (i : Fin 4 → h.J) (T : Fin 4 → (A₀.left ⟶ A₀.left)) {Z : Scheme.{0}} (a : Z ⟶ Y.H.left)
    (b : Z ⟶ A₀.left) (z : Z) (w : Z.presheaf.stalk z) : Prop :=
  gs a z (h.W (i 0) ⊓ xU Y α fun j => h.j (i j))
      (dE h ν (i 0) _ (rsT (xc Y α fun j => h.j (i j)).val (h.W (i 0) ⊓ xU Y α fun j => h.j (i j)))) =
    gs a z (xU Y α fun j => h.j (i j)) (xc Y α fun j => h.j (i j)).val *
      (- gs (b ≫ T 0) z (m₀ ⁻¹ᵁ V (i 0)) (pb (i 0)) + gs (b ≫ T 1) z (m₀ ⁻¹ᵁ V (i 1)) (pb (i 1)) -
        gs (b ≫ T 2) z (m₀ ⁻¹ᵁ V (i 2)) (pb (i 2)) + gs (b ≫ T 3) z (m₀ ⁻¹ᵁ V (i 3)) (pb (i 3)) + w)

def ChartFree (α : Q.X) : Prop :=
  ∀ (T : Fin 4 → (A₀.left ⟶ A₀.left)), (∀ j, T j ≫ m₀ = m₀ ≫ Q.famφB α j) → (∀ j, T j ≫ A₀.hom = A₀.hom) →
    ∀ (Z : Scheme.{0}) (a : Z ⟶ Y.H.left) (b : Z ⟶ A₀.left), a ≫ Y.q.left = b ≫ m₀ → ∀ (z : Z) (i i' : Fin 4 → h.J),
      (∀ j, (b ≫ T j ≫ m₀) z ∈ V (i j)) → (∀ j, (b ≫ T j ≫ m₀) z ∈ V (i' j)) → ∀ w,
        CoordAt Y h ν m₀ V pb α i T a b z w → CoordAt Y h ν m₀ V pb α i' T a b z w

def CoordEq (α : Q.X) (c : K) : Prop :=
  ∀ (T : Fin 4 → (A₀.left ⟶ A₀.left)), (∀ j, T j ≫ m₀ = m₀ ≫ Q.famφB α j) → (∀ j, T j ≫ A₀.hom = A₀.hom) →
    ∀ (Z : Scheme.{0}) (a : Z ⟶ Y.H.left) (b : Z ⟶ A₀.left), a ≫ Y.q.left = b ≫ m₀ → ∀ (z : Z) (i : Fin 4 → h.J),
      (∀ j, (b ≫ T j ≫ m₀) z ∈ V (i j)) → CoordAt Y h ν m₀ V pb α i T a b z (cst (b ≫ A₀.hom) z c)

theorem ext_lift {U : A₀.left.Opens} {f g : Γ(A₀.left, U)}
    (H : ∀ (Z : Scheme.{0}) (a : Z ⟶ Y.H.left) (b : Z ⟶ A₀.left), a ≫ Y.q.left = b ≫ m₀ → ∀ z : Z, b z ∈ U →
      gs b z U f = gs b z U g) : f = g := by
  have := Y.smooth_q
  have := (AbConst.surjective_q Y).1
  refine FunDescent.app_injective (pullback.snd Y.q.left m₀) U (fn_ext fun z hz => ?_)
  have e := H _ _ _ pullback.condition z hz
  rw [gs_pull (𝟙 _) _ z U hz, gs_pull (𝟙 _) _ z U hz, Category.id_comp]
  exact e

variable {Y h ν m₀} {φ : R →+* K} {e : ℕ} [GrpObj A₀] (hF : IsFibre Y h φ e ν A₀ m₀)
include hF

theorem IsFibre.gs_const {Z : Scheme.{0}} {a : Z ⟶ Y.H.left} {b : Z ⟶ A₀.left} (w : a ≫ Y.q.left = b ≫ m₀) (z : Z)
    (U : Y.H.left.Opens) (hz : a z ∈ U) (r : R) : gs a z U (constFn Y.H.hom U r) = cst (b ≫ A₀.hom) z (φ r) := by
  have e₁ : a ≫ Y.H.hom = (b ≫ A₀.hom) ≫ spMap φ := by
    rw [← Over.w Y.q, reassoc_of% w, hF.pull.1.w, Category.assoc]
  rw [gs_constFn _ _ _ _ hz, e₁, cst, cst, ← gs_pull _ (spMap φ) z ⊤ trivial]
  exact congrArg (gs _ z ⊤) (congrArg (fun ψ => ψ.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))).symm

theorem IsFibre.exists_strictHenselian_absolutely_closed_local_ring (α : Q.X) : ∃ T : Fin 4 → (A₀.left ⟶ A₀.left),
    (∀ j, T j ≫ m₀ = m₀ ≫ Q.famφB α j) ∧ ∀ j, T j ≫ A₀.hom = A₀.hom := by
  have P := hF.pull.1
  have w : ∀ j, (m₀ ≫ Q.famφB α j) ≫ Q.P.A.hom = A₀.hom ≫ spMap φ := fun j => by
    have : Q.famφB α j ≫ Q.P.A.hom = Q.P.A.hom := by
      fin_cases j
      exacts [Category.id_comp _, Over.w _, Over.w _, Over.w _]
    rw [Category.assoc, this, P.w]
  exact ⟨fun j => P.lift _ _ (w j), fun j => P.lift_fst _ _ _, fun j => P.lift_snd _ _ _⟩

theorem IsFibre.dE_agree [CharZero K] {Z : Scheme.{0}} {a : Z ⟶ Y.H.left} {b : Z ⟶ A₀.left}
    (w : a ≫ Y.q.left = b ≫ m₀) (z : Z) (i i' : h.J) (U : Y.H.left.Opens) (hU : U ≤ h.W i ⊓ h.W i') (hz : a z ∈ U)
    (f : Γ(Y.H.left, U)) : gs a z U (dE h ν i U f) = gs a z U (dE h ν i' U f) := by
  have := AbConst.lift_agree h hF.field i i' U hU (gsH a z U hz)
    (by simpa only [map_ofNat] using (two_ne_zero (α := K)).isUnit.map (cstH (b ≫ A₀.hom) z))
    (fun a' b' => by rw [← gs_eq_gsH, hF.gs_const w z U hz, hF.symb, cst_eq_cstH, map_zero]) f
  simp only [gs_eq_gsH a z U hz, dE, map_add, this]

theorem IsFibre.T_zero {α : Q.X} {T : A₀.left ⟶ A₀.left} (h₁ : T ≫ m₀ = m₀ ≫ Q.famφB α 0) (h₂ : T ≫ A₀.hom = A₀.hom) :
    T = 𝟙 _ :=
  hF.pull.1.hom_ext (h₁.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
    (h₂.trans (Category.id_comp _).symm)

variable {V ed pb}

theorem IsFibre.mem_chart (hD : IsDesc Y h ν m₀ V ed pb) (hV : ∀ i, V i ≤ Q.P.L.U (h.j i)) {α : Q.X}
    {T : Fin 4 → (A₀.left ⟶ A₀.left)} (h₁ : ∀ j, T j ≫ m₀ = m₀ ≫ Q.famφB α j) {Z : Scheme.{0}} {a : Z ⟶ Y.H.left}
    {b : Z ⟶ A₀.left} (w : a ≫ Y.q.left = b ≫ m₀) {z : Z} {i : Fin 4 → h.J} (hi : ∀ j, (b ≫ T j ≫ m₀) z ∈ V (i j)) :
    a z ∈ h.W (i 0) ⊓ xU Y α fun j => h.j (i j) := by
  have e : ∀ j, b ≫ T j ≫ m₀ = a ≫ Y.q.left ≫ Q.famφB α j := fun j => by rw [h₁, reassoc_of% w]
  refine ⟨?_, Set.mem_iInter.2 fun k => ?_⟩
  · have := hi 0
    rw [e, show Q.famφB α 0 = 𝟙 _ from rfl, Category.comp_id] at this
    rw [hD.1]
    exact this
  · have := hV _ (hi (![1, 2, 0, 3] k))
    rw [e, ← gtφT_eq] at this
    exact this

end Ray

end GlobalTheory.HeatConn
