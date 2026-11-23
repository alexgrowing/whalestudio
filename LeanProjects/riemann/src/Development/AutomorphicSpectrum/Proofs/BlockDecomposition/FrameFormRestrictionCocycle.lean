import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalisationLadders.CriterionTruncation
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.GrPull
noncomputable section
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C}

theorem prod_mem_fil {Fil : ℤ → IdF Φ.A} (hF : IsFil Φ Fil) (T : C) :
    ∀ (n : ℕ) (g : Fin n → Φ.A.obj T), (∀ k, g k ∈ Φ.J.S T) → ∏ k, g k ∈ (Fil n).S T
  | 0, g, _ => by
    have h := hF.top 0 le_rfl T
    simp only [Nat.cast_zero, h]
    exact Submodule.mem_top
  | n + 1, g, h => by
    rw [Fin.prod_univ_castSucc]
    have h1 : g (Fin.last n) ∈ (Fil ((1 : ℕ) : ℤ)).S T := by
      rw [Nat.cast_one, hF.one]; exact h _
    exact hF.mul n 1 T (prod_mem_fil hF T n _ fun k => h _) h1

variable {d : ℕ} {E : Frame Φ (d + 1)} (Q : Poly Φ) (σ : ∀ T : C, E.D ⟶ T)

theorem tau_sec_Pmap (i : Fin d) {T T' : C} (φ : T ⟶ T') :
    E.τ i.succ (Cut.sec Q ⟨T, σ T⟩ ≫ Cut.Pmap Q (X := ⟨T, σ T⟩) (Y := ⟨T', σ T'⟩) φ) (Cut.sec Q ⟨T', σ T'⟩) =
      (Φ.A.map (Q.j T')).hom (E.τ i.succ (σ T ≫ φ) (σ T')) := by
  rw [Cut.τ_sec, if_neg (Fin.succ_ne_zero i), neg_zero, zero_add]
  have e : σ T ≫ Q.j T ≫ Cut.Pmap Q (X := ⟨T, σ T⟩) (Y := ⟨T', σ T'⟩) φ = (σ T ≫ φ) ≫ Q.j T' := by
    have := Cut.Pmap_j Q (X := ⟨T, σ T⟩) (Y := ⟨T', σ T'⟩) φ
    simp only at this
    rw [this, Category.assoc]
  simp only
  rw [e, E.add i.succ _ (σ T' ≫ Q.j T') _, E.nat]
  have h := Cut.sec_spec Q (E := E) ⟨T', σ T'⟩ i.succ
  simp only at h
  rw [h, if_neg (Fin.succ_ne_zero i), add_zero]

theorem factor {T₀ T₁ T₂ : C} (i : Fin d) (b : T₀ ⟶ T₁) (a : T₁ ⟶ T₂) :
    (Φ.A.map (Cut.Pmap Q (X := ⟨T₁, σ T₁⟩) (Y := ⟨T₂, σ T₂⟩) a)).hom
      (E.τ i.succ (Cut.sec Q ⟨T₀, σ T₀⟩ ≫ Cut.Pmap Q (X := ⟨T₀, σ T₀⟩) (Y := ⟨T₁, σ T₁⟩) b) (Cut.sec Q ⟨T₁, σ T₁⟩)) =
      (Φ.A.map (Q.j T₂)).hom ((Φ.A.map a).hom (E.τ i.succ (σ T₀ ≫ b) (σ T₁))) := by
  rw [tau_sec_Pmap, ← Cut.mapA_comp, ← Cut.mapA_comp]
  have := Cut.Pmap_j Q (X := ⟨T₁, σ T₁⟩) (Y := ⟨T₂, σ T₂⟩) a
  simp only at this
  rw [this]

variable {Fil : ℤ → IdF Φ.A}

theorem form_sub_mem (hF : IsFil Φ Fil) (hc : E.GrConst Fil) (j q : ℕ) (r : ℤ) (hr : r = j + q)
    (I : Fin j → Fin d) (x : Φ.A.obj E.D) (hx : x ∈ (Fil q).S E.D) (s : ComposableArrows C j) :
    (show Φ.A.obj (Q.P (s.obj (Fin.last j))) from (Cut.E1 E).form Cut.can I x (s ⋙ Cut.Pσ Q σ)) -
      (Φ.A.map (Q.j (s.obj (Fin.last j)))).hom (E.form σ (Fin.succ ∘ I) x s) ∈
        (Fil (r + 1)).S (Q.P (s.obj (Fin.last j))) := by
  have e1 : ∀ k : Fin j, ((Cut.Φ1 E).A.map ((s ⋙ Cut.Pσ Q σ).map (homOfLE (Fin.le_last k.succ)))).hom
      ((Cut.E1 E).a Cut.can (I k) ((s ⋙ Cut.Pσ Q σ).map (homOfLE (Fin.castSucc_lt_succ (i := k)).le))) =
      (Φ.A.map (Q.j (s.obj (Fin.last j)))).hom ((Φ.A.map (s.map (homOfLE (Fin.le_last k.succ)))).hom
        (E.a σ ((Fin.succ ∘ I) k) (s.map (homOfLE (Fin.castSucc_lt_succ (i := k)).le)))) :=
    fun k => factor Q σ (I k) _ _
  let P₀ : Φ.A.obj (s.obj (Fin.last j)) := ∏ k : Fin j, (Φ.A.map (s.map (homOfLE (Fin.le_last k.succ)))).hom
    (E.a σ ((Fin.succ ∘ I) k) (s.map (homOfLE (Fin.castSucc_lt_succ (i := k)).le)))
  have hP : P₀ ∈ (Fil j).S (s.obj (Fin.last j)) :=
    prod_mem_fil hF _ j _ fun k => Φ.J.map_mem _ (E.mem _ _ _)
  let u : E.D ⟶ Q.P (s.obj (Fin.last j)) := Cut.sec Q ⟨s.obj (Fin.last j), σ _⟩
  let v : E.D ⟶ Q.P (s.obj (Fin.last j)) := σ (s.obj (Fin.last j)) ≫ Q.j _
  have f1 : (show Φ.A.obj (Q.P (s.obj (Fin.last j))) from (Cut.E1 E).form Cut.can I x (s ⋙ Cut.Pσ Q σ)) =
      (Φ.A.map (Q.j (s.obj (Fin.last j)))).hom P₀ * (Φ.A.map u).hom x := by
    have h : (∏ k : Fin j, (show Φ.A.obj (Q.P (s.obj (Fin.last j))) from
        ((Cut.Φ1 E).A.map ((s ⋙ Cut.Pσ Q σ).map (homOfLE (Fin.le_last k.succ)))).hom
          ((Cut.E1 E).a Cut.can (I k) ((s ⋙ Cut.Pσ Q σ).map (homOfLE (Fin.castSucc_lt_succ (i := k)).le))))) =
        (Φ.A.map (Q.j (s.obj (Fin.last j)))).hom P₀ :=
      (Finset.prod_congr rfl fun k _ => e1 k).trans (map_prod (Φ.A.map (Q.j (s.obj (Fin.last j)))).hom _ _).symm
    exact congrArg (· * (Φ.A.map u).hom x) h
  have f2 : (Φ.A.map (Q.j (s.obj (Fin.last j)))).hom (E.form σ (Fin.succ ∘ I) x s) =
      (Φ.A.map (Q.j (s.obj (Fin.last j)))).hom P₀ * (Φ.A.map v).hom x := by
    change (Φ.A.map (Q.j (s.obj (Fin.last j)))).hom (P₀ * (Φ.A.map (σ _)).hom x) = _
    rw [map_mul, ← Cut.mapA_comp]
  rw [f1, f2, ← mul_sub]
  have hcast : r + 1 = ((j + (q + 1) : ℕ) : ℤ) := by rw [hr]; push_cast; ring
  rw [hcast]
  refine hF.mul j (q + 1) _ ((Fil j).map_mem _ hP) ?_
  have := hc q u v hx
  have e : ((q + 1 : ℕ) : ℤ) = (q : ℤ) + 1 := by push_cast; rfl
  rw [e]
  exact this

theorem gr_pull {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} (Q : Poly Φ) {Fil : ℤ → IdF Φ.A}
    (hF : IsFil Φ Fil) {d : ℕ} (E : Frame Φ (d + 1)) (σ : ∀ T : C, E.D ⟶ T) (hc : E.GrConst Fil) (j q : ℕ) (r : ℤ) (hr : r = j + q)
    (I : Fin j → Fin d) (x : Φ.A.obj E.D) (hx : x ∈ (Fil q).S E.D)
    (f : CH.Cn (Cut.U E ⋙ gr Fil r) j) (g : CH.Cn (gr Fil r) j)
    (hf : ∀ s, (show sqM _ _ _ from f s).1 = Ideal.Quotient.mk _ ((Cut.E1 E).form Cut.can I x s))
    (hg : ∀ s, (show sqM _ _ _ from g s).1 = Ideal.Quotient.mk _ (E.form σ (Fin.succ ∘ I) x s)) :
    (CH.Mor.restrict (Cut.U E ⋙ gr Fil r) (Cut.Pσ Q σ)).pullC j f =
      (CH.Mor.ofNatTrans (Functor.whiskerRight (Cut.jσ Q σ) (gr Fil r))).pullC j g := by
  funext s
  refine Subtype.ext ?_
  have h1 := hf (s ⋙ Cut.Pσ Q σ)
  have h2 := hg s
  change (show sqM _ _ _ from f (s ⋙ Cut.Pσ Q σ)).1 =
    Ideal.quotientMapₐ _ (Φ.A.map (Q.j (s.obj (Fin.last j)))).hom (fun _ hx => (Fil (r + 1)).map_mem _ hx)
      (show sqM _ _ _ from g s).1
  rw [h1, h2]
  exact Ideal.Quotient.eq.2 (form_sub_mem Q σ hF hc j q r hr I x hx s)

end
end GlobalTheory.CompanionTheory.GrPull
