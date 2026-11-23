import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LeISupInfPreimage

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KS (rsT pbT)
open GlobalTheory.LogKS (IsField)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Heat.Gauge

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {n : ℕ} {X : Scheme.{0}}
  (m : G.left ⟶ X) {m₁ : G.left ⟶ X} {L : LB X} {dd : Fin n → Fld G.left} {D : R → R} (h₁ : Heat G m₁ L dd D)

def W (p : h₁.J × (Fin 2 → L.ι)) : G.left.Opens := h₁.W p.1 ⊓ LB.wchart L ![m, m₁] p.2

theorem heatGaugeCoverOpen_le_heatOperatorOpen (p : h₁.J × (Fin 2 → L.ι)) : W m h₁ p ≤ h₁.W p.1 := inf_le_left

theorem W_le_wchart (p : h₁.J × (Fin 2 → L.ι)) : W m h₁ p ≤ LB.wchart L ![m, m₁] p.2 := inf_le_right

theorem W_le_m (p : h₁.J × (Fin 2 → L.ι)) : W m h₁ p ≤ m ⁻¹ᵁ L.U (p.2 0) :=
  (W_le_wchart m h₁ p).trans (LB.wchart_le L ![m, m₁] p.2 0)

theorem W_le_m₁ (p : h₁.J × (Fin 2 → L.ι)) : W m h₁ p ≤ m₁ ⁻¹ᵁ (L.U (p.2 1) ⊓ L.U (h₁.j p.1)) :=
  fun _ hy => ⟨LB.wchart_le L ![m, m₁] p.2 1 hy.2, h₁.le p.1 hy.1⟩

variable (e : LB.Gen (LB.LinComb L ![m, m₁] ![1, -1]))

def gU (p : h₁.J × (Fin 2 → L.ι)) : Γ(G.left, W m h₁ p)ˣ :=
  res (W_le_wchart m h₁ p) (e.s p.2) * res (W_le_m₁ m h₁ p) (pullU m₁ _ (L.g (p.2 1) (h₁.j p.1)))

def gL (a : Fin n) (p : h₁.J × (Fin 2 → L.ι)) : Γ(G.left, W m h₁ p) :=
  dd a (W m h₁ p) (gU m h₁ e p).val * (gU m h₁ e p)⁻¹.val

def gE (p : h₁.J × (Fin 2 → L.ι)) : Γ(G.left, W m h₁ p) :=
  h₁.d p.1 (W m h₁ p) (gU m h₁ e p).val * (gU m h₁ e p)⁻¹.val

def gY (a : Fin n) (p : h₁.J × (Fin 2 → L.ι)) : Γ(G.left, W m h₁ p) :=
  ∑ b, constFn G.hom (W m h₁ p) (h₁.Θ a b) * gL m h₁ e b p

def gD (p : h₁.J × (Fin 2 → L.ι)) : Fld G.left :=
  fun O f => h₁.d p.1 O f + ∑ a, rsT (gY m h₁ e a p) O * dd a O f

def gP (c : R) (p : h₁.J × (Fin 2 → L.ι)) : Γ(G.left, W m h₁ p) :=
  rsT (h₁.p p.1) (W m h₁ p) - gE m h₁ e p -
    constFn G.hom (W m h₁ p) c * ∑ a, ∑ b, constFn G.hom (W m h₁ p) (h₁.Θ a b) * gL m h₁ e a p * gL m h₁ e b p

def gP' (c : R) (p : h₁.J × (Fin 2 → L.ι)) : Γ(G.left, W m h₁ p) :=
  rsT (h₁.p' p.1) (W m h₁ p) +
    constFn G.hom (W m h₁ p) c * ∑ a, ∑ b, constFn G.hom (W m h₁ p) (h₁.Θ a b) * dd a (W m h₁ p) (gL m h₁ e b p) -
    ∑ a, constFn G.hom (W m h₁ p) (h₁.u a) * gL m h₁ e a p

theorem isField_mono {Z : Scheme.{0}} {W₀ W₁ : Z.Opens} {d : Fld Z} (h : IsField W₀ d) (hle : W₁ ≤ W₀) :
    IsField W₁ d :=
  ⟨fun W hW => h.1 W (hW.trans hle), fun W hW => h.2.1 W (hW.trans hle),
    fun W W' hWW' hW => h.2.2 W W' hWW' (hW.trans hle)⟩

open GlobalTheory.KS in

theorem op_rsT {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] {n : ℕ}
    (dd : Fin n → Fld G.left) (hdd : ∀ a, IsField ⊤ (dd a)) (Θ : Matrix (Fin n) (Fin n) R) (u : Fin n → R)
    (d : Fld G.left) {W₀ : G.left.Opens} (p p' : Γ(G.left, W₀)) (k : ℕ) {O O' : G.left.Opens}
    (hd : IsField O d) (hO : O ≤ W₀) (h : O' ≤ O) (f : Γ(G.left, O)) :
    rsT (op G dd Θ u d p p' k O f) O' = op G dd Θ u d p p' k O' (rsT f O') := by
  have hd' : ∀ g, resG G.left h (d O g) = d O' (resG G.left h g) :=
    fun g => (hd.2.2 O O' h le_rfl g).symm
  have hdd' : ∀ a g, resG G.left h (dd a O g) = dd a O' (resG G.left h g) :=
    fun a g => ((hdd a).2.2 O O' h le_top g).symm
  have hc : ∀ r, resG G.left h (constFn G.hom O r) = constFn G.hom O' r :=
    fun r => (rsT_of_le h _).symm.trans (rsT_constFn G.hom h r)
  have hp : ∀ q : Γ(G.left, W₀), resG G.left h (rsT q O) = rsT q O' := fun q => by
    rw [← rsT_of_le h, rsT_rsT hO h]
  rw [rsT_of_le h, rsT_of_le h]
  simp only [op, map_add, map_sub, map_mul, map_sum, map_pow, map_natCast, map_ofNat, hd', hdd', hc, hp]

theorem trans_factor {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R) {O : Type} [CommRing O] [StarRing O]
    [Module O Q.X] (oa : Q.OAct O) (Y : GlobalTheory.RayEv.Ray oa) (x : 𝟙_ (Over (Sp R)) ⟶ Y.H) :
    ∃ τ : Q.P.A.left ⟶ Q.P.A.left, (𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left = Y.q.left ≫ τ := by
  haveI : IsMonHom Y.q := Y.q_linear.isMonHom
  refine ⟨(𝟙 Q.P.A * (toUnit Q.P.A ≫ x ≫ Y.q)).left, ?_⟩
  have e : (𝟙 Y.H * (toUnit Y.H ≫ x)) ≫ Y.q = Y.q ≫ (𝟙 Q.P.A * (toUnit Q.P.A ≫ x ≫ Y.q)) := by
    rw [MonObj.mul_comp, MonObj.comp_mul, Category.id_comp, Category.comp_id, ← Category.assoc Y.q (toUnit _),
      toUnit_unique (Y.q ≫ toUnit Q.P.A) (toUnit Y.H), Category.assoc]
  exact congrArg (fun f => f.left) e

end GlobalTheory.Heat.Gauge
