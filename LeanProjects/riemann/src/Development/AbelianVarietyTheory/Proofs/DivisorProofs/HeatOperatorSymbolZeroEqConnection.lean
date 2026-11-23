import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConnK
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectionClosedFibreEqDerivationIdentificationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorConnectionClosedFibreStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LogDerivativePrincipalPolarisationIndependent
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ConstThickeningFieldStructure
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
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.HeatUConn

open GlobalTheory.KS.DlogPol (gs_rsT gs_pbT gs_one gs_sub gs_constFn)

theorem val_zpow_eps {S : Type} [CommRing S] (ee : S) (hee : ee * ee = 0) (E : Sˣ) (a : S) (hE : E.val = 1 + ee * a)
    (n : ℤ) : (E ^ n).val = 1 + (n : S) * ee * a := by
  induction n using Int.induction_on with
  | zero => simp
  | succ n ih =>
    rw [zpow_add_one, Units.val_mul, ih, hE]; push_cast; linear_combination ((n : S) * a * a) * hee
  | pred n ih =>
    have hi : (E⁻¹).val = 1 - ee * a :=
      Units.inv_eq_of_mul_eq_one_right (by rw [hE]; linear_combination (-(a * a)) * hee)
    rw [zpow_sub_one, Units.val_mul, ih, hi]; push_cast; linear_combination ((n : S) * a * a) * hee

theorem gs_natCast {Z Y : Scheme.{0}} (f : Z ⟶ Y) (z : Z) (O : Y.Opens) (hz : f z ∈ O) (n : ℕ) :
    gs f z O (n : Γ(Y, O)) = n := by
  rw [gs_eq f z O hz, map_natCast, map_natCast]

theorem gs_ofNat {Z Y : Scheme.{0}} (f : Z ⟶ Y) (z : Z) (O : Y.Opens) (hz : f z ∈ O) (n : ℕ) [n.AtLeastTwo] :
    gs f z O (OfNat.ofNat n : Γ(Y, O)) = OfNat.ofNat n := by
  rw [gs_eq f z O hz, map_ofNat, map_ofNat]

theorem gs_intCast {Z Y : Scheme.{0}} (f : Z ⟶ Y) (z : Z) (O : Y.Opens) (hz : f z ∈ O) (n : ℤ) :
    gs f z O (n : Γ(Y, O)) = n := by
  rw [gs_eq f z O hz, map_intCast, map_intCast]

theorem gs_sum {Z Y : Scheme.{0}} (f : Z ⟶ Y) (z : Z) (O : Y.Opens) (hz : f z ∈ O) {I : Type} (s : Finset I)
    (a : I → Γ(Y, O)) : gs f z O (∑ i ∈ s, a i) = ∑ i ∈ s, gs f z O (a i) := by
  simp only [gs_eq f z O hz, map_sum]

def cstD {k : Type} [Field k] {Z : Scheme.{0}} (p : Z ⟶ Sp (DualNumber k)) (z : Z) :
    DualNumber k →+* Z.presheaf.stalk z :=
  (Z.presheaf.germ (p ⁻¹ᵁ ⊤) z trivial).hom.comp ((p.app ⊤).hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).inv.hom)

theorem gs_cstD {k : Type} [Field k] {Z : Scheme.{0}} (p : Z ⟶ Sp (DualNumber k)) (z : Z) (a : DualNumber k) :
    gs p z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).inv.hom a) = cstD p z a :=
  gs_eq p z ⊤ trivial _

theorem gs_spMap {A' B'' : Type} [CommRing A'] [CommRing B''] {Z : Scheme.{0}} (p : Z ⟶ Sp B'') (g : A' →+* B'')
    (z : Z) (a : A') :
    gs (p ≫ spMap g) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A')).inv.hom a) =
      gs p z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of B'')).inv.hom (g a)) := by
  rw [← gs_pull p (spMap g) z ⊤ trivial]
  have := congrArg (fun φ => φ.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom g))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
  rw [this]
  rfl

end GlobalTheory.HeatUConn

namespace GlobalTheory.HeatUConn

open GlobalTheory.KS.DlogPol (gs_rsT gs_pbT gs_one gs_sub gs_constFn)

theorem prod_one_add_eps {S : Type} [CommRing S] (ee : S) (hee : ee * ee = 0) {I : Type} (s : Finset I) (b : I → S) :
    ∏ j ∈ s, (1 + ee * b j) = 1 + ee * ∑ j ∈ s, b j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ih]
    linear_combination (b a * ∑ j ∈ s, b j) * hee

theorem zpow_sum_u {G I : Type} [CommGroup G] (a : G) (s : Finset I) (f : I → ℤ) :
    a ^ (∑ i ∈ s, f i) = ∏ i ∈ s, a ^ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert b s hb ih => rw [Finset.sum_insert hb, Finset.prod_insert hb, zpow_add, ih]

theorem prod3 {G : Type} [CommGroup G] (f g h : Fin 4 → G) (n : Fin 4 → ℤ) :
    ∏ j, (f j * (g j)⁻¹ * h j) ^ n j = (∏ j, f j ^ n j) * (∏ j, g j ^ n j)⁻¹ * ∏ j, h j ^ n j := by
  simp only [mul_zpow, inv_zpow, Finset.prod_mul_distrib, Finset.prod_inv_distrib]

theorem final_alg {S : Type} [CommRing S] (T1 T1i T2 s d K Sg C H E e' : S) (hU : T1 * T1i = 1)
    (hH : H * (2 * e') = 1) (hEE : E * E = 0) :
    T1 * (s + E * d) * (T2 * T1i * (K * (1 + E * Sg))) =
      K * (1 + -C * E) * (T2 * s + H * E * (T2 * (2 * e' * (d + s * (Sg + C))))) := by
  linear_combination (T2 * K * (s + E * d) * (1 + E * Sg)) * hU + (-(T2 * K * E * (Sg * s + d + C * s))) * hH +
    (T2 * K * (d * Sg + 2 * e' * H * C * (d + s * Sg + s * C))) * hEE

theorem gm_pull_g {X X' Y : Scheme.{0}} {L : LB X} (F : X' ⟶ X) (f : Y ⟶ X') (y : Y) (j j' : L.ι)
    (hj : F (f y) ∈ L.U j) (hj' : F (f y) ∈ L.U j') :
    gm f y ((L.pull F).U (fun _ => j) ⊓ (L.pull F).U (fun _ => j')) ((L.pull F).g (fun _ => j) (fun _ => j')) =
      gm (f ≫ F) y _ (L.g j j') := by
  have hp : f y ∈ (L.pull F).U (fun _ => j) ⊓ (L.pull F).U (fun _ => j') := ⟨mem_pull.2 hj, mem_pull.2 hj'⟩
  show gm f y _ (∏ _k : PUnit, (res _ (pullU F _ (L.g j j'))) ^ (1 : ℤ)) = _
  rw [Fintype.prod_unique, zpow_one]
  exact (gm_res f y _ hp _).trans (gm_pull f F y (L.U j ⊓ L.U j') ⟨hj, hj'⟩ _)

example {X Y Z : Scheme.{0}} (f : Z ⟶ Y) (g : Y ⟶ X) (z : Z) : (f ≫ g) z = g (f z) := rfl

end GlobalTheory.HeatUConn

namespace GlobalTheory.HeatUConn

open GlobalTheory.KS.DlogPol (gs_rsT gs_pbT gs_one gs_sub gs_constFn)

theorem core {R : Type} [CommRing R] {k : Type} [Field k] [CharZero k] (A : Over (Sp R)) (L : LB A.left)
    (B' : Over (Sp (DualNumber k))) (π₁ π₂ : B'.left ⟶ A.left) (hpt : ∀ b : B'.left, π₁ b = π₂ b)
    (A₀ : Over (Sp k)) (m₀ : A₀.left ⟶ A.left) (pr : B'.left ⟶ A₀.left) (hpr : pr ≫ m₀ = π₂)
    (hpr' : pr ≫ A₀.hom = B'.hom ≫ spMap (algebraMap k (DualNumber k)))
    {J' : Type} (V : J' → A.left.Opens) (jj : J' → L.ι) (hV : ⨆ i, V i = ⊤) (hVU : ∀ i, V i ≤ L.U (jj i))
    (ed : ∀ W : A.left.Opens, Γ(A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W)) (pb : ∀ i, Γ(A₀.left, m₀ ⁻¹ᵁ V i))
    (hA : ∀ (W : A.left.Opens) (f : Γ(A.left, W)), pbT π₁ f (π₂ ⁻¹ᵁ W) = pbT π₂ f (π₂ ⁻¹ᵁ W) +
      constFn B'.hom (π₂ ⁻¹ᵁ W) DualNumber.eps * pbT pr (ed W f) (π₂ ⁻¹ᵁ W))
    (w : LB.Iso (L.pull π₁) (L.pull π₂)) (hw : w.IsGen) (κ : (DualNumber k)ˣ)
    (hκ : ∀ i, rsT (w.s (fun _ => jj i, fun _ => jj i)).val (π₂ ⁻¹ᵁ V i) = constFn B'.hom (π₂ ⁻¹ᵁ V i) κ.val *
      (1 + constFn B'.hom (π₂ ⁻¹ᵁ V i) DualNumber.eps * pbT pr (pb i) (π₂ ⁻¹ᵁ V i)))
    (e : ℕ) (he : 1 ≤ e) (fam : Fin 4 → (A.left ⟶ A.left)) (es : Fin 4 → ℤ) (hes : ∑ j, es j = e)
    (σ σ' : LB.Sec (LB.LinComb L fam es)) (T : Fin 4 → (A₀.left ⟶ A₀.left)) (hT : ∀ j, T j ≫ m₀ = m₀ ≫ fam j)
    (c0 : k)
    (hF : ∀ (i : Fin 4 → J') (O : A₀.left.Opens), O ≤ m₀ ⁻¹ᵁ LB.wchart L fam (fun j => jj (i j)) →
      (∀ j, O ≤ T j ⁻¹ᵁ (m₀ ⁻¹ᵁ V (i j))) → pbT m₀ (σ'.f (fun j => jj (i j))) O =
        2 * (e : Γ(A₀.left, O)) * (rsT (ed _ (σ.f (fun j => jj (i j)))) O + pbT m₀ (σ.f (fun j => jj (i j))) O *
          (∑ j, ((es j : ℤ) : Γ(A₀.left, O)) * pbT (T j) (pb (i j)) O + constFn A₀.hom O c0)))
    (Z : Scheme.{0}) (x : Z ⟶ B'.left) (xs : Fin 4 → (Z ⟶ B'.left))
    (hxs : ∀ j, xs j ≫ π₁ = (x ≫ π₁) ≫ fam j ∧ xs j ≫ π₂ = (x ≫ π₂) ≫ fam j ∧ xs j ≫ B'.hom = x ≫ B'.hom)
    (hxpr : ∀ j, xs j ≫ pr = (x ≫ pr) ≫ T j) (z : Z) (J : (Z ⟶ A.left) → L.ι) (hJ : Good L z J) :
    sval σ (x ≫ π₁) z J *
        (∏ j, gm (xs j) z _ (w.s (fun _ => J (xs j ≫ π₂), fun _ => J (xs j ≫ π₁))) ^ es j).val =
      gs (x ≫ B'.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).inv.hom
        ((κ ^ e).val * (1 + TrivSqZeroExt.inr (-c0)))) *
      (sval σ (x ≫ π₂) z J + gs (x ≫ B'.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).inv.hom
        (TrivSqZeroExt.inr ((2 * (e : k))⁻¹))) * sval σ' (x ≫ π₂) z J) := by
  have hpz : (x ≫ π₁) z = (x ≫ π₂) z := hpt (x z)
  choose i hi using fun j : Fin 4 =>
    TopologicalSpace.Opens.mem_iSup.1 (show ((x ≫ π₂) ≫ fam j) z ∈ ⨆ i, V i by rw [hV]; trivial)
  set t : Fin 4 → L.ι := fun j => jj (i j) with ht
  have hmem₂ : (x ≫ π₂) z ∈ LB.wchart L fam t := Set.mem_iInter.2 fun j => hVU (i j) (hi j)
  have hmem₁ : (x ≫ π₁) z ∈ LB.wchart L fam t := by rw [hpz]; exact hmem₂

  have sa : sval σ (x ≫ π₁) z J = (trF fam es (x ≫ π₁) z (fun k => J ((x ≫ π₁) ≫ fam k)) t).val *
      gs (x ≫ π₁) z (LB.wchart L fam t) (σ.f t) := sec_trans σ (x ≫ π₁) z (hJ.mem fam _) hmem₁
  have sb : sval σ (x ≫ π₂) z J = (trF fam es (x ≫ π₂) z (fun k => J ((x ≫ π₂) ≫ fam k)) t).val *
      gs (x ≫ π₂) z (LB.wchart L fam t) (σ.f t) := sec_trans σ (x ≫ π₂) z (hJ.mem fam _) hmem₂
  have sc : sval σ' (x ≫ π₂) z J = (trF fam es (x ≫ π₂) z (fun k => J ((x ≫ π₂) ≫ fam k)) t).val *
      gs (x ≫ π₂) z (LB.wchart L fam t) (σ'.f t) := sec_trans σ' (x ≫ π₂) z (hJ.mem fam _) hmem₂

  set E : Z.presheaf.stalk z := cstD (x ≫ B'.hom) z DualNumber.eps with hE
  have hEE : E * E = 0 := by rw [hE, ← map_mul, DualNumber.eps_mul_eps, map_zero]
  have le12 : ∀ W : A.left.Opens, π₂ ⁻¹ᵁ W ≤ π₁ ⁻¹ᵁ W := fun W b hb => by
    show π₁ b ∈ W; rw [hpt]; exact hb
  have le2p : ∀ W : A.left.Opens, π₂ ⁻¹ᵁ W ≤ pr ⁻¹ᵁ (m₀ ⁻¹ᵁ W) := fun W b hb => by
    show m₀ (pr b) ∈ W; rw [← Scheme.Hom.comp_apply, hpr]; exact hb

  have hA' : gs (x ≫ π₁) z (LB.wchart L fam t) (σ.f t) = gs (x ≫ π₂) z (LB.wchart L fam t) (σ.f t) +
      E * gs (x ≫ pr) z (m₀ ⁻¹ᵁ LB.wchart L fam t) (ed _ (σ.f t)) := by
    have h := congrArg (gs x z (π₂ ⁻¹ᵁ LB.wchart L fam t)) (hA (LB.wchart L fam t) (σ.f t))
    have hxz : x z ∈ π₂ ⁻¹ᵁ LB.wchart L fam t := hmem₂
    erw [gs_pbT x π₁ z (le12 (LB.wchart L fam t)) hxz] at h
    rw [gs_add _ _ _ hxz, gs_mul _ _ _ hxz] at h
    erw [gs_pbT x π₂ z le_rfl hxz, gs_pbT x pr z (le2p (LB.wchart L fam t)) hxz] at h
    rw [GlobalTheory.KS.DlogPol.gs_constFn _ _ _ _ hxz, gs_cstD] at h
    exact h

  have hPG := (isGen_iff w).1 hw
  have p2 : ∀ j, (xs j ≫ π₂) z = ((x ≫ π₂) ≫ fam j) z := fun j => by rw [(hxs j).2.1]
  have p1 : ∀ j, (xs j ≫ π₁) z = ((x ≫ π₂) ≫ fam j) z := fun j => by
    rw [(hxs j).1]; show fam j ((x ≫ π₁) z) = fam j ((x ≫ π₂) z); rw [hpz]
  have hgw : ∀ j, gm (xs j) z _ (w.s (fun _ => J (xs j ≫ π₂), fun _ => J (xs j ≫ π₁))) =
      gm (xs j ≫ π₂) z _ (L.g (J (xs j ≫ π₂)) (t j)) * (gm (xs j ≫ π₁) z _ (L.g (J (xs j ≫ π₁)) (t j)))⁻¹ *
        gw w (xs j) z (t j) (fun _ => t j) := fun j => by
    have h4 : π₁ (xs j z) ∈ L.U (t j) := by
      show (xs j ≫ π₁) z ∈ L.U (t j); rw [p1]; exact hVU _ (hi j)
    have := hPG Z (xs j) z (J (xs j ≫ π₂)) (t j) (fun _ => J (xs j ≫ π₁)) (fun _ => t j) (hJ _)
      (by show (xs j ≫ π₂) z ∈ L.U (t j); rw [p2]; exact hVU _ (hi j)) (mem_pull.2 (hJ _)) (mem_pull.2 h4)
    rw [gm_pull_g π₁ (xs j) z _ _ (hJ _) h4] at this
    exact this
  have hK : ∀ j, (gw w (xs j) z (t j) (fun _ => t j)).val = cstD (x ≫ B'.hom) z κ.val *
      (1 + E * gs ((x ≫ pr) ≫ T j) z (m₀ ⁻¹ᵁ V (i j)) (pb (i j))) := fun j => by
    have hx : xs j z ∈ π₂ ⁻¹ᵁ V (i j) := by show (xs j ≫ π₂) z ∈ V (i j); rw [p2]; exact hi j
    have hle : π₂ ⁻¹ᵁ V (i j) ≤ (L.pull π₂).U (fun _ => t j) ⊓ (L.pull π₁).U (fun _ => t j) := fun b hb =>
      ⟨mem_pull.2 (hVU (i j) (show π₂ b ∈ V (i j) from hb)),
        mem_pull.2 (show π₁ b ∈ L.U (t j) by rw [hpt]; exact hVU (i j) hb)⟩
    have h := congrArg (gs (xs j) z (π₂ ⁻¹ᵁ V (i j))) (hκ (i j))
    erw [gs_rsT _ _ hle hx, gs_unit _ _ _ (hle hx)] at h
    rw [gs_mul _ _ _ hx, GlobalTheory.KS.DlogPol.gs_constFn _ _ _ _ hx,
      gs_add _ _ _ hx, gs_one _ _ _ hx, gs_mul _ _ _ hx, GlobalTheory.KS.DlogPol.gs_constFn _ _ _ _ hx] at h
    erw [gs_pbT (xs j) pr z (le2p _) hx] at h
    rw [(hxs j).2.2, hxpr j, gs_cstD, gs_cstD] at h
    exact h

  set O : A₀.left.Opens := m₀ ⁻¹ᵁ LB.wchart L fam t ⊓ T 0 ⁻¹ᵁ (m₀ ⁻¹ᵁ V (i 0)) ⊓ T 1 ⁻¹ᵁ (m₀ ⁻¹ᵁ V (i 1)) ⊓
    T 2 ⁻¹ᵁ (m₀ ⁻¹ᵁ V (i 2)) ⊓ T 3 ⁻¹ᵁ (m₀ ⁻¹ᵁ V (i 3)) with hO
  have hO1 : O ≤ m₀ ⁻¹ᵁ LB.wchart L fam t :=
    inf_le_left.trans (inf_le_left.trans (inf_le_left.trans inf_le_left))
  have hO2 : ∀ j, O ≤ T j ⁻¹ᵁ (m₀ ⁻¹ᵁ V (i j)) := fun j => by
    fin_cases j
    · exact inf_le_left.trans (inf_le_left.trans (inf_le_left.trans inf_le_right))
    · exact inf_le_left.trans (inf_le_left.trans inf_le_right)
    · exact inf_le_left.trans inf_le_right
    · exact inf_le_right
  have cpr : (x ≫ pr) ≫ m₀ = x ≫ π₂ := by rw [Category.assoc, hpr]
  have cT : ∀ j, ((x ≫ pr) ≫ T j) ≫ m₀ = (x ≫ π₂) ≫ fam j := fun j => by
    rw [Category.assoc, hT j, ← Category.assoc, cpr]
  have mT : ∀ j, ((x ≫ pr) ≫ T j) z ∈ m₀ ⁻¹ᵁ V (i j) := fun j => by
    show (((x ≫ pr) ≫ T j) ≫ m₀) z ∈ V (i j); rw [cT]; exact hi j
  have hxO : (x ≫ pr) z ∈ O := by
    refine ⟨⟨⟨⟨?_, mT 0⟩, mT 1⟩, mT 2⟩, mT 3⟩
    show ((x ≫ pr) ≫ m₀) z ∈ LB.wchart L fam t; rw [cpr]; exact hmem₂
  set a : Fin 4 → Z.presheaf.stalk z := fun j => gs ((x ≫ pr) ≫ T j) z (m₀ ⁻¹ᵁ V (i j)) (pb (i j)) with ha
  have hFz : gs (x ≫ π₂) z (LB.wchart L fam t) (σ'.f t) = 2 * (e : Z.presheaf.stalk z) *
      (gs (x ≫ pr) z (m₀ ⁻¹ᵁ LB.wchart L fam t) (ed _ (σ.f t)) + gs (x ≫ π₂) z (LB.wchart L fam t) (σ.f t) *
        (∑ j, (es j : Z.presheaf.stalk z) * a j + cstD (x ≫ B'.hom) z (algebraMap k (DualNumber k) c0))) := by
    have h := congrArg (gs (x ≫ pr) z O) (hF i O hO1 hO2)
    rw [← ht] at h
    have hterm : ∀ j, gs (x ≫ pr) z O (((es j : ℤ) : Γ(A₀.left, O)) * pbT (T j) (pb (i j)) O) =
        (es j : Z.presheaf.stalk z) * a j := fun j => by
      rw [gs_mul _ _ _ hxO, gs_intCast _ _ _ hxO, gs_pbT _ _ z (hO2 j) hxO]
    have hc : (x ≫ pr) ≫ A₀.hom = (x ≫ B'.hom) ≫ spMap (algebraMap k (DualNumber k)) := by
      rw [Category.assoc, hpr', Category.assoc]
    have e1 : gs (x ≫ pr) z O (pbT m₀ (σ'.f t) O) = gs (x ≫ π₂) z (LB.wchart L fam t) (σ'.f t) :=
      (gs_pbT (x ≫ pr) m₀ z hO1 hxO (σ'.f t)).trans (by rw [cpr])
    have e2 : gs (x ≫ pr) z O (pbT m₀ (σ.f t) O) = gs (x ≫ π₂) z (LB.wchart L fam t) (σ.f t) :=
      (gs_pbT (x ≫ pr) m₀ z hO1 hxO (σ.f t)).trans (by rw [cpr])
    have e3 : gs (x ≫ pr) z O (rsT (ed _ (σ.f t)) O) =
        gs (x ≫ pr) z (m₀ ⁻¹ᵁ LB.wchart L fam t) (ed _ (σ.f t)) := gs_rsT _ _ hO1 hxO _
    rw [e1, gs_mul _ _ _ hxO, gs_mul _ _ _ hxO, gs_ofNat _ _ _ hxO, gs_natCast _ _ _ hxO, gs_add _ _ _ hxO, e3,
      gs_mul _ _ _ hxO, e2, gs_add _ _ _ hxO, gs_sum _ _ _ hxO,
      GlobalTheory.KS.DlogPol.gs_constFn _ _ _ _ hxO, hc, gs_spMap, gs_cstD] at h
    simp only [hterm] at h
    exact h

  set φ := cstD (x ≫ B'.hom) z with hφ
  have key : ∀ f g : Z ⟶ A.left, f = g → ∀ b : L.ι, gm f z (L.U (J f) ⊓ L.U b) (L.g (J f) b) =
      gm g z (L.U (J g) ⊓ L.U b) (L.g (J g) b) := by rintro f _ rfl b; rfl
  have htr1 : ∏ j, (gm (xs j ≫ π₁) z _ (L.g (J (xs j ≫ π₁)) (t j))) ^ es j =
      trF fam es (x ≫ π₁) z (fun k => J ((x ≫ π₁) ≫ fam k)) t :=
    Finset.prod_congr rfl fun j _ => by rw [key _ _ (hxs j).1]
  have htr2 : ∏ j, (gm (xs j ≫ π₂) z _ (L.g (J (xs j ≫ π₂)) (t j))) ^ es j =
      trF fam es (x ≫ π₂) z (fun k => J ((x ≫ π₂) ≫ fam k)) t :=
    Finset.prod_congr rfl fun j _ => by rw [key _ _ (hxs j).2.1]
  let κu : (Z.presheaf.stalk z)ˣ := Units.map φ.toMonoidHom κ
  have hκu : ∀ n : ℕ, (κu ^ n).val = φ (κ ^ n).val := fun n => by
    rw [← map_pow]; rfl
  set Ej : Fin 4 → (Z.presheaf.stalk z)ˣ := fun j => κu⁻¹ * gw w (xs j) z (t j) (fun _ => t j) with hEjd
  have hEj : ∀ j, (Ej j).val = 1 + E * a j := fun j => by
    rw [hEjd]
    rw [Units.val_mul, hK j]
    have h1 : (κu⁻¹).val * κu.val = 1 := Units.inv_mul κu
    have h2 : κu.val = φ κ.val := rfl
    rw [← h2]
    linear_combination (1 + E * a j) * h1
  have hKprod : (∏ j, (gw w (xs j) z (t j) (fun _ => t j)) ^ es j).val =
      φ (κ ^ e).val * (1 + E * ∑ j, (es j : Z.presheaf.stalk z) * a j) := by
    have hsplit : ∀ j, gw w (xs j) z (t j) (fun _ => t j) = κu * Ej j :=
      fun j => (mul_inv_cancel_left κu _).symm
    rw [Finset.prod_congr rfl fun j _ => by rw [hsplit j]]
    simp only [mul_zpow, Finset.prod_mul_distrib]
    rw [← zpow_sum_u, hes, zpow_natCast, Units.val_mul, hκu, Units.coe_prod]
    simp only [fun j => val_zpow_eps E hEE _ (a j) (hEj j) (es j)]
    rw [← prod_one_add_eps E hEE Finset.univ (fun j => (es j : Z.presheaf.stalk z) * a j)]
    congr 1
    exact Finset.prod_congr rfl fun j _ => by ring
  have hinr : ∀ r : k, φ (TrivSqZeroExt.inr r) = φ (algebraMap k (DualNumber k) r) * E := fun r => by
    rw [DualNumber.inr_eq_smul_eps, Algebra.smul_def, map_mul]
  have h2e : (2 * (e : k)) ≠ 0 := by
    have : (e : k) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    exact mul_ne_zero two_ne_zero this
  have hH : φ (algebraMap k (DualNumber k) (2 * (e : k))⁻¹) * (2 * (e : Z.presheaf.stalk z)) = 1 := by
    have : φ (algebraMap k (DualNumber k) (2 * (e : k))) = 2 * (e : Z.presheaf.stalk z) := by
      simp [map_mul, map_natCast, map_ofNat]
    rw [← this, ← map_mul, ← map_mul, inv_mul_cancel₀ h2e, map_one, map_one]
  have hU : (trF fam es (x ≫ π₁) z (fun k => J ((x ≫ π₁) ≫ fam k)) t).val *
      ((trF fam es (x ≫ π₁) z (fun k => J ((x ≫ π₁) ≫ fam k)) t)⁻¹).val = 1 := Units.mul_inv _
  rw [gs_cstD, gs_cstD, sa, sb, sc, hA', hFz]
  simp only [hgw]
  rw [prod3, htr1, htr2, Units.val_mul, Units.val_mul, hKprod, map_mul, map_add, map_one, hinr, hinr]
  simp only [map_neg]
  exact final_alg _ _ _ _ _ _ _ _ _ _ _ hU hH hEE

end GlobalTheory.HeatUConn

namespace GlobalTheory.HeatUConn

theorem uconn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n' : ℕ) (v' : Module.Basis (Fin n') (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n' → Fld Y.H.left), (∀ a, IsInv Y.H (v' a) (dd a)) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → (∀ a b, h.Θ a b ∈ maximalIdeal (ChartRing k m d)) → ∀ ρ : ChartRing k m d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (D r))) → ∀ (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ P.D.toPre.P.A.left) (c' : P.D.toPre.X → (Sp (DualNumber k) ⟶ B'.left)), IsGrpPullback B' P.D.toPre.P.A (spMap ρ) π₁ → IsGrpPullback B' P.D.toPre.P.A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → (∀ y, c' y ≫ B'.hom = 𝟙 _ ∧ c' y ≫ π₁ = spMap ρ ≫ (P.D.toPre.c y).left ∧ c' y ≫ π₂ = spMap (constHom ρ) ≫ (P.D.toPre.c y).left) → ∀ w : LB.Iso (P.D.toPre.P.L.pull π₁) (P.D.toPre.P.L.pull π₂), w.IsGen → ∃ (κ : ℕ → (DualNumber k)ˣ) (ℓ : ℕ → P.D.toPre.X →+ k), ∀ (e : ℕ), 1 ≤ e → ∀ (α : P.D.toPre.X) (σ σ' : P.D.toPre.SecB e α), TActs Y h e α σ σ' → ∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (xs : Fin 4 → (Z ⟶ B'.left)), (∀ j, xs j ≫ π₁ = (x ≫ π₁) ≫ P.D.toPre.famφB α j ∧ xs j ≫ π₂ = (x ≫ π₂) ≫ P.D.toPre.famφB α j ∧ xs j ≫ B'.hom = x ≫ B'.hom) → ∀ z J, Good P.D.toPre.P.L z J → sval σ (x ≫ π₁) z J * (∏ j, gm (xs j) z _ (w.s (fun _ => J (xs j ≫ π₂), fun _ => J (xs j ≫ π₁))) ^ DegPre.famε e j).val = gs (x ≫ B'.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).inv.hom ((κ e).val * (1 + TrivSqZeroExt.inr (ℓ e α)))) * (sval σ (x ≫ π₂) z J + gs (x ≫ B'.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).inv.hom (TrivSqZeroExt.inr ((2 * (e : k))⁻¹))) * sval σ' (x ≫ π₂) z J) := by
  intro E _ _ _ H k _ _ m d t P gam hmon hlin hab
  letI := H.starRing
  intro Y n' v' dd hdd D q hq h hB hdef hΘ ρ hρ B' _ π₁ π₂ c' hπ₁ hπ₂ hcl hc' w hw
  obtain ⟨A₀, _, m₀, hA₀⟩ : ∃ (A₀ : Over (Sp k)) (_ : GrpObj A₀) (m₀ : A₀.left ⟶ P.D.toPre.P.A.left),
      IsGrpPullback A₀ P.D.toPre.P.A (spMap ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ)) m₀ :=
    ⟨_, _, _, isGrpPullback_pullback _ _⟩
  have hcs : spMap (constHom ρ) = spMap (algebraMap k (DualNumber k)) ≫
      spMap ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ) := by
    unfold constHom; rw [← Spec.map_comp]; rfl
  let pr : B'.left ⟶ A₀.left := hA₀.1.lift π₂ (B'.hom ≫ spMap (algebraMap k (DualNumber k))) (by
    rw [hπ₂.1.w, hcs, Category.assoc])
  have hpr : pr ≫ m₀ = π₂ := hA₀.1.lift_fst _ _ _
  have hpr' : pr ≫ A₀.hom = B'.hom ≫ spMap (algebraMap k (DualNumber k)) := hA₀.1.lift_snd _ _ _
  have hpt : ∀ b : B'.left, π₁ b = π₂ b := by
    have P0 := IsPullback.of_hasPullback B'.hom (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)
    have hs : Surjective (pullback.fst B'.hom (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)) :=
      MorphismProperty.of_isPullback (P := @Surjective) P0.flip GlobalTheory.ConstThickening.surjective_spMap_fst
    intro b
    obtain ⟨b0, rfl⟩ := hs.surj b
    exact congrArg (fun f => f b0) (hcl _ _ _ pullback.condition)
  have key : ∀ e : ℕ, ∃ (κ : (DualNumber k)ˣ) (ℓ : P.D.toPre.X →+ k), 1 ≤ e → ∀ (α : P.D.toPre.X)
      (σ σ' : P.D.toPre.SecB e α), TActs Y h e α σ σ' → ∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left)
      (xs : Fin 4 → (Z ⟶ B'.left)), (∀ j, xs j ≫ π₁ = (x ≫ π₁) ≫ P.D.toPre.famφB α j ∧
        xs j ≫ π₂ = (x ≫ π₂) ≫ P.D.toPre.famφB α j ∧ xs j ≫ B'.hom = x ≫ B'.hom) →
      ∀ z J, Good P.D.toPre.P.L z J → sval σ (x ≫ π₁) z J * (∏ j, gm (xs j) z _
          (w.s (fun _ => J (xs j ≫ π₂), fun _ => J (xs j ≫ π₁))) ^ DegPre.famε e j).val =
        gs (x ≫ B'.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).inv.hom
          (κ.val * (1 + TrivSqZeroExt.inr (ℓ α)))) *
        (sval σ (x ≫ π₂) z J + gs (x ≫ B'.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).inv.hom
          (TrivSqZeroExt.inr ((2 * (e : k))⁻¹))) * sval σ' (x ≫ π₂) z J) := by
    intro e
    by_cases he : 1 ≤ e
    · obtain ⟨V, ed, pb, hconn, -, hF⟩ := GlobalTheory.T.heatOperator_connection_closedFibre E H k m d t P gam hmon hlin hab Y n' v' dd hdd D q hq h hB
        hdef hΘ ρ hρ e he A₀ m₀ hA₀
      obtain ⟨hA, κ, hκ⟩ := GlobalTheory.T.connection_closedFibre_eq_derivation_identification k (ChartRing k m d) P.D.toPre.P ρ B' π₁ π₂ hπ₁ hπ₂ hcl A₀ m₀ hA₀ pr hpr
        hpr' V h.j ed pb hconn w hw
      obtain ⟨c, hc⟩ := hF B' π₁ π₂ c' hπ₁ hπ₂ hcl hc' pr hpr hpr' hA
      refine ⟨κ ^ e, -c, fun _ α σ σ' hTA Z x xs hxs z J hJ => ?_⟩
      have hfam : ∀ j, P.D.toPre.famφB α j ≫ P.D.toPre.P.A.hom = P.D.toPre.P.A.hom := by
        intro j
        fin_cases j <;> simp [DegPre.famφB]
      let T : Fin 4 → (A₀.left ⟶ A₀.left) := fun j => hA₀.1.lift (m₀ ≫ P.D.toPre.famφB α j) A₀.hom (by
        rw [Category.assoc, hfam, hA₀.1.w])
      have hT : ∀ j, T j ≫ m₀ = m₀ ≫ P.D.toPre.famφB α j := fun j => hA₀.1.lift_fst _ _ _
      have hTh : ∀ j, T j ≫ A₀.hom = A₀.hom := fun j => hA₀.1.lift_snd _ _ _
      have hxpr : ∀ j, xs j ≫ pr = (x ≫ pr) ≫ T j := fun j => hA₀.1.hom_ext
        (by
          have hprA : ∀ {W : Scheme.{0}} (f : P.D.toPre.P.A.left ⟶ W), pr ≫ m₀ ≫ f = π₂ ≫ f := fun f => by
            rw [← Category.assoc, hpr]
          simp only [Category.assoc, hpr, hT, hprA, (hxs j).2.1])
        (by rw [Category.assoc, hpr', ← Category.assoc, (hxs j).2.2, Category.assoc, Category.assoc, hTh,
          Category.assoc, hpr'])
      have hes : ∑ j, DegPre.famε e j = (e : ℤ) := by
        simp [DegPre.famε, Fin.sum_univ_four]
      have := core P.D.toPre.P.A P.D.toPre.P.L B' π₁ π₂ hpt A₀ m₀ pr hpr hpr' V h.j hconn.2.1 hconn.2.2.1 ed pb hA w hw
        κ hκ e he (P.D.toPre.famφB α) (DegPre.famε e) hes σ σ' T hT (c α)
        (fun i O h1 h2 => hc α σ σ' hTA i T hT hTh O h1 h2) Z x xs hxs hxpr z J hJ
      simpa using this
    · exact ⟨1, 0, fun h' => absurd h' he⟩
  choose κ ℓ hκℓ using key
  exact ⟨κ, ℓ, fun e he α σ σ' hT Z x xs hxs z J hJ => hκℓ e he α σ σ' hT Z x xs hxs z J hJ⟩

end GlobalTheory.HeatUConn
