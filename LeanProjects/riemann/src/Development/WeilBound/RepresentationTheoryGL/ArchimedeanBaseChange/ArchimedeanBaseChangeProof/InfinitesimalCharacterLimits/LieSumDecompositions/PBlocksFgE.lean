import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PBlocksFgD

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs GlobalTheory.SmGL

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockFiniteGeneration

set_option linter.unusedSectionVars false

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r s : ℕ}

theorem collect {α β : Type} (S : Finset α) (X : Set β) (Q : α → Finset β → Prop)
    (hmono : ∀ a (F F' : Finset β), F ⊆ F' → Q a F → Q a F')
    (h : ∀ a ∈ S, ∃ F : Finset β, (↑F : Set β) ⊆ X ∧ Q a F) :
    ∃ F : Finset β, (↑F : Set β) ⊆ X ∧ ∀ a ∈ S, Q a F := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨∅, by simp, by simp⟩
  | insert a S ha ih =>
    obtain ⟨F, hF, hQ⟩ := ih fun b hb => h b (Finset.mem_insert_of_mem hb)
    obtain ⟨F', hF', hQ'⟩ := h a (Finset.mem_insert_self a S)
    refine ⟨F ∪ F', by rw [Finset.coe_union]; exact Set.union_subset hF hF', fun b hb => ?_⟩
    rcases Finset.mem_insert.1 hb with rfl | hb
    · exact hmono _ _ _ Finset.subset_union_right hQ'
    · exact hmono _ _ _ Finset.subset_union_left (hQ b hb)

theorem finGL_unip' {N k : ℕ} (x : BlockIx N k → Af E) :
    finGL E N (unip x) = unip (fun p => sFin E (x p)) := by
  apply Units.ext
  change 1 - (1 : Matrix (Fin N) (Fin N) (Af E)).map (sFin E) + (1 + nilM x).map (sFin E) = 1 + nilM _
  rw [Matrix.map_add _ (map_add (sFin E))]
  have : (nilM x).map (sFin E) = nilM (r := k) (fun p => sFin E (x p)) := by
    ext i j
    simp only [nilM, Matrix.map_apply, Matrix.of_apply]
    split_ifs <;> simp
  rw [this]; abel

theorem cover (L : Subgroup (GL (Fin (r + s)) (Af E))) (hL : IsOpen (L : Set (GL (Fin (r + s)) (Af E)))) :
    ∃ Tf : Finset (GL (Fin (r + s)) (Af E)), ∀ g : GL (Fin (r + s)) (Af E),
      ∃ (x : BlockIx (r + s) r → Af E) (a : GL (Fin r) (Af E)) (b : GL (Fin s) (Af E)) (t l : GL (Fin (r + s)) (Af E)),
        t ∈ Tf ∧ l ∈ L ∧ g = unip x * lev (Af E) r s (a, b) * t * l := by
  obtain ⟨Tf, hTf⟩ := IwaAd.exists_finset_cover E (r + s) L hL
  refine ⟨Tf, fun g => ?_⟩
  obtain ⟨x, m, c, hc, rfl⟩ := IwaFin.exists_unip_lev_integral E r s g
  obtain ⟨t, ht, l, hl, rfl⟩ := hTf c hc
  exact ⟨x, m.1, m.2, t, l, ht, hl, by rw [← mul_assoc]⟩

theorem yp_decomp (k : Kinf E (r + s)) (x : BlockIx (r + s) r → Af E) (a : GL (Fin r) (Af E))
    (b : GL (Fin s) (Af E)) (t l : GL (Fin (r + s)) (Af E)) :
    BlockDerivatives.yp k (unip x * lev (Af E) r s (a, b) * t * l) =
      unip (fun p => sFin E (x p)) * lev (Ad E) r s (finGL E r a, finGL E s b) * BlockDerivatives.yp k t * finGL E (r + s) l := by
  have hP : finGL E (r + s) (unip x * lev (Af E) r s (a, b)) =
      unip (fun p => sFin E (x p)) * lev (Ad E) r s (finGL E r a, finGL E s b) := by
    rw [map_mul, finGL_unip', Slice1.lev_finGL]
  rw [← hP, BlockDerivatives.yp, BlockDerivatives.yp]
  have e : finGL E (r + s) (unip x * lev (Af E) r s (a, b) * t * l) =
      finGL E (r + s) (unip x * lev (Af E) r s (a, b)) * finGL E (r + s) t * finGL E (r + s) l := by
    rw [map_mul, map_mul]
  rw [e]
  simp only [mul_assoc]
  rw [← mul_assoc (infGL E (r + s) (Unitary.toUnits k)) (finGL E (r + s) (unip x * lev (Af E) r s (a, b))),
    infGL_comm, mul_assoc]

theorem yp_one_fin {a : ℕ} (h : GL (Fin a) (Af E)) : BlockDerivatives.yp (1 : Kinf E a) h = finGL E a h := by
  simp [BlockDerivatives.yp]

theorem grp_step (m : GA E r × GA E s) (x : BlockIx (r + s) r → Af E) (a : GL (Fin r) (Af E)) (b : GL (Fin s) (Af E))
    (y : GA E (r + s)) (z : GA E (r + s)) :
    ∃ v : BlockIx (r + s) r → Ad E, lev (Ad E) r s m * (unip (fun p => sFin E (x p)) *
        lev (Ad E) r s (finGL E r a, finGL E s b) * y * z) =
      unip v * (lev (Ad E) r s (m.1 * finGL E r a, m.2 * finGL E s b) * y) * z := by
  obtain ⟨v, hv⟩ := InducedTensorMap.lev_mul_unip m (fun p => sFin E (x p))
  refine ⟨v, ?_⟩
  have e : lev (Ad E) r s (m.1 * finGL E r a, m.2 * finGL E s b) =
      lev (Ad E) r s m * lev (Ad E) r s (finGL E r a, finGL E s b) := by
    rw [← map_mul]; rfl
  rw [e]
  simp only [mul_assoc]
  rw [← mul_assoc (lev (Ad E) r s m) (unip _), hv]
  simp only [mul_assoc]

theorem slice_decomp_left (F : Sm E (r + s)) (hu : ∀ (x : BlockIx (r + s) r → Ad E) g, F.1 (unip x * g) = F.1 g)
    (l : GL (Fin (r + s)) (Af E)) (hl : ∀ y, F.1 (y * finGL E (r + s) l) = F.1 y) (k : Kinf E (r + s))
    (x : BlockIx (r + s) r → Af E) (a : GL (Fin r) (Af E)) (b : GL (Fin s) (Af E)) (t : GL (Fin (r + s)) (Af E))
    (m₂ : GA E s) :
    sl0 m₂ (rt E (r + s) (BlockDerivatives.yp k (unip x * lev (Af E) r s (a, b) * t * l)) F) =
      act (.fin a) (sl0 (m₂ * finGL E s b) (rt E (r + s) (BlockDerivatives.yp k t) F)) := by
  refine Subtype.ext (funext fun m₁ => ?_)
  have L : (sl0 m₂ (rt E (r + s) (BlockDerivatives.yp k (unip x * lev (Af E) r s (a, b) * t * l)) F)).1 m₁ =
      F.1 (lev (Ad E) r s (m₁, m₂) * BlockDerivatives.yp k (unip x * lev (Af E) r s (a, b) * t * l)) := by
    rw [left_slice_apply, rt_apply]
  have R : (act (.fin a) (sl0 (m₂ * finGL E s b) (rt E (r + s) (BlockDerivatives.yp k t) F))).1 m₁ =
      F.1 (lev (Ad E) r s (m₁ * finGL E r a, m₂ * finGL E s b) * BlockDerivatives.yp k t) := by
    rw [act_fin_eq, rt_apply, yp_one_fin, left_slice_apply, rt_apply]
  rw [L, R, yp_decomp]
  obtain ⟨v, hv⟩ := grp_step (m₁, m₂) x a b (BlockDerivatives.yp k t) (finGL E (r + s) l)
  rw [hv, hl, hu]

theorem slice_decomp_right (F : Sm E (r + s)) (hu : ∀ (x : BlockIx (r + s) r → Ad E) g, F.1 (unip x * g) = F.1 g)
    (l : GL (Fin (r + s)) (Af E)) (hl : ∀ y, F.1 (y * finGL E (r + s) l) = F.1 y) (k : Kinf E (r + s))
    (x : BlockIx (r + s) r → Af E) (a : GL (Fin r) (Af E)) (b : GL (Fin s) (Af E)) (t : GL (Fin (r + s)) (Af E))
    (m₁ : GA E r) :
    sl1 m₁ (rt E (r + s) (BlockDerivatives.yp k (unip x * lev (Af E) r s (a, b) * t * l)) F) =
      act (.fin b) (sl1 (m₁ * finGL E r a) (rt E (r + s) (BlockDerivatives.yp k t) F)) := by
  refine Subtype.ext (funext fun m₂ => ?_)
  have L : (sl1 m₁ (rt E (r + s) (BlockDerivatives.yp k (unip x * lev (Af E) r s (a, b) * t * l)) F)).1 m₂ =
      F.1 (lev (Ad E) r s (m₁, m₂) * BlockDerivatives.yp k (unip x * lev (Af E) r s (a, b) * t * l)) := by
    rw [right_slice_apply, rt_apply]
  have R : (act (.fin b) (sl1 (m₁ * finGL E r a) (rt E (r + s) (BlockDerivatives.yp k t) F))).1 m₂ =
      F.1 (lev (Ad E) r s (m₁ * finGL E r a, m₂ * finGL E s b) * BlockDerivatives.yp k t) := by
    rw [act_fin_eq, rt_apply, yp_one_fin, right_slice_apply, rt_apply]
  rw [L, R, yp_decomp]
  obtain ⟨v, hv⟩ := grp_step (m₁, m₂) x a b (BlockDerivatives.yp k t) (finGL E (r + s) l)
  rw [hv, hl, hu]

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockFiniteGeneration
