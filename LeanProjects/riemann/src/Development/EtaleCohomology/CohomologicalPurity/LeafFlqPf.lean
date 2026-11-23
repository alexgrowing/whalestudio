import Development.EtaleCohomology.CohomologicalPurity.LeafClCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.Cl.Flq

abbrev ZN {R : Type} [CommRing R] (K : Cx R) {X : Scheme.{0}} (U : X.Opens) (n : ℤ) (W : X.Opens) :
    AddSubgroup (Sec (K.X n) W.toScheme) := Zc K (W.ι ⁻¹ᵁ U) n

def BN {R : Type} [CommRing R] (K : Cx R) {X : Scheme.{0}} (U : X.Opens) (n : ℤ) (W : X.Opens) :
    AddSubgroup (Sec (K.X n) W.toScheme) := AddSubgroup.closure {a | Bd K (W.ι ⁻¹ᵁ U) n a}

abbrev OK {R : Type} [CommRing R] {G : Shv R} {X : Scheme.{0}} (N : ∀ W : X.Opens, AddSubgroup (Sec G W.toScheme)) : Prop :=
  (∀ (V W : X.Opens) (h : V ≤ W), ∀ a ∈ N W, rs h a ∈ N V) ∧
  (∀ (W : X.Opens) (a : Sec G W.toScheme), (∀ x ∈ W, ∃ (V : X.Opens) (h : V ≤ W), x ∈ V ∧ rs h a ∈ N V) → a ∈ N W) ∧
  (∀ (V W : X.Opens) (h : V ≤ W), ∀ a ∈ N V, ∃ b ∈ N W, rs h b = a)

def LeafBdAdd : Prop := ∀ (R : Type) [CommRing R] (K : Cx R) (X : Scheme.{0}) (U : X.Opens) (n : ℤ) (W : X.Opens)
  (a : Sec (K.X n) W.toScheme), a ∈ BN K U n W → Bd K (W.ι ⁻¹ᵁ U) n a

def LeafBZ : Prop := ∀ (R : Type) [CommRing R] (K : Cx R) (X : Scheme.{0}) (U : X.Opens) (n : ℤ) (W : X.Opens)
  (a : Sec (K.X n) W.toScheme), Bd K (W.ι ⁻¹ᵁ U) n a → a ∈ ZN K U n W

def LeafZloc : Prop := ∀ (R : Type) [CommRing R] (K : Cx R) (X : Scheme.{0}) (U : X.Opens) (n : ℤ),
  (∀ (V W : X.Opens) (h : V ≤ W), ∀ a ∈ ZN K U n W, rs h a ∈ ZN K U n V) ∧
  (∀ (W : X.Opens) (a : Sec (K.X n) W.toScheme), (∀ x ∈ W, ∃ (V : X.Opens) (h : V ≤ W), x ∈ V ∧ rs h a ∈ ZN K U n V) →
    a ∈ ZN K U n W)

def LeafZero : Prop := ∀ (R : Type) [CommRing R] (K : Cx R) (X : Scheme.{0}) (U : X.Opens) (n : ℤ),
  IsZero (K.X n) → OK (ZN K U n)

def LeafStep : Prop := ∀ (R : Type) [CommRing R] (K : Cx R), LateralTheory.CohomologicalPurity.Cl.LeafZorn → (∀ s, Injective (K.X s)) →
  ∀ (X : Scheme.{0}) (U : X.Opens) (n : ℤ), OK (ZN K U (n - 1)) → OK (BN K U n)

def LeafTop : Prop := ∀ (R : Type) [CommRing R] (K : Cx R) (X : Scheme.{0}) (U : X.Opens) (n : ℤ)
  (c' : Sec (K.X n) (⊤ : X.Opens).toScheme), c' ∈ ZN K U n ⊤ →
  ∃ c ∈ Zc K U n, ∀ V : X.Opens, Sec.res V.ι c = rs le_top c'

def LeafRs : Prop := ∀ (R : Type) [CommRing R] (G : Shv R) (X : Scheme.{0}) (T V W : X.Opens) (h : V ≤ W) (h' : T ≤ V)
  (a b : Sec G W.toScheme), rs h (a - b) = rs h a - rs h b ∧ rs h' (rs h a) = rs (h'.trans h) a

theorem LeafRs_of : LeafRs := by
  intro R _ G X T V W h h' a b
  refine ⟨?_, ?_⟩
  · show ((G.obj.map (X.homOfLE h).op).hom (a - b)) = _
    exact map_sub _ a b
  · show ((G.obj.map (X.homOfLE h').op).hom ((G.obj.map (X.homOfLE h).op).hom a)) = (G.obj.map (X.homOfLE (h'.trans h)).op).hom a
    have e : X.homOfLE (h'.trans h) = X.homOfLE h' ≫ X.homOfLE h := (Scheme.homOfLE_homOfLE X h' h).symm
    rw [e, op_comp, Functor.map_comp]
    rfl

theorem LeafFlq_of (hZ : LateralTheory.CohomologicalPurity.Cl.LeafZorn) (hA : LeafBdAdd) (hBZ : LeafBZ) (hL : LeafZloc) (h0 : LeafZero)
    (hS : LeafStep) (hT : LeafTop) : LateralTheory.CohomologicalPurity.Cl.LeafFlq := by
  intro R _ K hinj hneg X U m H
  have hR := LeafRs_of
  have key : ∀ n, n < m → OK (ZN K U (n - 1)) → OK (ZN K U n) := by
    intro n hn hprev
    have hB := hS R K hZ hinj X U n hprev
    have eq : ZN K U n = BN K U n := by
      funext W; ext a; constructor
      · intro ha; apply hB.2.1 W a; intro x hx
        obtain ⟨V, h, hxV, hb⟩ := H n hn W a ha x hx
        exact ⟨V, h, hxV, AddSubgroup.subset_closure hb⟩
      · intro ha; exact hBZ R K X U n W a (hA R K X U n W a ha)
    rw [eq]; exact hB
  have P : ∀ k : ℕ, (k : ℤ) < m → OK (ZN K U (k : ℤ)) := by
    intro k
    induction k with
    | zero => intro h; exact key _ h (h0 R K X U _ (hneg _ (by norm_num)))
    | succ k ih =>
      intro h
      apply key _ h
      have e : ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) := by push_cast; ring
      rw [e]; exact ih (by omega)
  have hm : OK (ZN K U (m - 1)) := by
    by_cases hc : m - 1 < 0
    · exact h0 R K X U _ (hneg _ hc)
    · have e : ((m - 1).toNat : ℤ) = m - 1 := Int.toNat_of_nonneg (by omega)
      have := P (m - 1).toNat (by omega)
      rw [e] at this; exact this
  have hBm := hS R K hZ hinj X U m hm
  refine ⟨fun W a hloc => hA R K X U m W a (hBm.2.1 W a fun x hx => ?_), ?_⟩
  · obtain ⟨V, h, hxV, hb⟩ := hloc x hx
    exact ⟨V, h, hxV, AddSubgroup.subset_closure hb⟩
  intro A V a ha hcov hagree
  obtain ⟨c', hc'⟩ := hZ R (K.X m) X (BN K U m) hBm.1 hBm.2.1 hBm.2.2 ⊤ A V (fun _ => le_top) a
    (fun x _ => hcov x) (by
      intro k l
      apply hBm.2.1
      intro x hx
      obtain ⟨hxk, hxl⟩ := hx
      obtain ⟨T, hk, hl, hxT, hb⟩ := hagree k l x hxk hxl
      refine ⟨T, le_inf hk hl, hxT, ?_⟩
      have e : rs (le_inf hk hl) (rs (inf_le_left : V k ⊓ V l ≤ V k) (a k) - rs (inf_le_right : V k ⊓ V l ≤ V l) (a l))
          = rs hk (a k) - rs hl (a l) := by
        have rsub : ∀ {V W : X.Opens} (h : V ≤ W) (x y : Sec (K.X m) W.toScheme), rs h (x - y) = rs h x - rs h y :=
          fun {V W} h x y => (hR R _ X V V W h le_rfl x y).1
        have rrs : ∀ {T V W : X.Opens} (h : V ≤ W) (h' : T ≤ V) (x : Sec (K.X m) W.toScheme),
            rs h' (rs h x) = rs (h'.trans h) x := fun {T V W} h h' x => (hR R _ X T V W h h' x x).2
        rw [rsub, rrs, rrs]
      rw [e]; exact AddSubgroup.subset_closure hb)
  have hmem : c' ∈ ZN K U m ⊤ := by
    apply (hL R K X U m).2 ⊤ c'
    intro x _
    obtain ⟨k, hk⟩ := hcov x
    refine ⟨V k, le_top, hk, ?_⟩
    have h1 := hBZ R K X U m (V k) _ (hA R K X U m (V k) _ (hc' k))
    have h2 : a k ∈ ZN K U m (V k) := ha k
    simpa using add_mem h1 h2
  obtain ⟨c, hc, hcV⟩ := hT R K X U m c' hmem
  refine ⟨c, hc, fun k => ?_⟩
  rw [hcV]; exact hA R K X U m (V k) _ (hc' k)

end LateralTheory.CohomologicalPurity.Cl.Flq
