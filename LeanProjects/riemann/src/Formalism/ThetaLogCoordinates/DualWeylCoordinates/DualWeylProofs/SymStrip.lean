import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.QsColHStrip

noncomputable section

open Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

variable {n : ℕ} [NeZero n]

open Classical in

def qs_ps (b : ℕ) (mu nu : Fin n → ℤ) : Matrix (TIdx mu × SymIdx n b) (TIdx nu) ℤ := fun y K =>
  ∑ m : ↥(qs_D mu nu) → Fin n,
    if (∀ c : ↥(qs_D mu nu), m c ∈ qs_ext nu K c.1) ∧ qs_ext mu y.1 = qs_rem (qs_D mu nu) (qs_ext nu K) m then
      (if ∀ x, qs_cnt m x = (y.2.1 x : ℕ) then
        ∏ c : ↥(qs_D mu nu), qs_sg ((qs_ext nu K c.1).erase (m c)) (m c) else 0)
    else 0

open Classical in

def qs_mid (b : ℕ) (mu nu : Fin n → ℤ) (J : TIdx mu) (α : SymIdx n b) (K : TIdx nu) : GLCoord ℤ n :=
  ∑ a : ↥(qs_D mu nu) → Fin n, if (∀ x, qs_cnt a x = (α.1 x : ℕ)) then
    ((detU n ^ mu (lastIdx n) : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) *
      (if ∀ c : ↥(qs_D mu nu), a c ∉ qs_ext mu J c.1 then
        (∏ c : ↥(qs_D mu nu), ((qs_sg (qs_ext mu J c.1) (a c) : ℤ) : GLCoord ℤ n)) *
          ∏ c ∈ Finset.Ioc (mu (lastIdx n)) (nu 0),
            qs_mn (qs_gC n) (qs_add (qs_D mu nu) (qs_ext mu J) a c) (qs_ext nu K c) else 0)
  else 0

open Classical in
theorem qs_ps_left (b : ℕ) {mu nu : Fin n → ℤ} (hmu : Dominant mu) (hnu : Dominant nu) (hs : HStrip mu nu b)
    (J : TIdx mu) (α : SymIdx n b) (K : TIdx nu) :
    ∑ y : TIdx mu × SymIdx n b, TMat mu J y.1 * SymMat n b α y.2 * ((qs_ps b mu nu y K : ℤ) : GLCoord ℤ n) =
      qs_mid b mu nu J α K := by
  have hT : ∀ I, TMat mu J I = qs_TM (mu (lastIdx n)) (Finset.Ioc (mu (lastIdx n)) (nu 0)) (qs_ext mu J) (qs_ext mu I) :=
    fun I => qs_TMat_eq hmu _ _ le_rfl (hs.1 0) J I
  have hm : ∀ m : ↥(qs_D mu nu) → Fin n,
      ∑ y : TIdx mu × SymIdx n b, TMat mu J y.1 * SymMat n b α y.2 *
        (((if (∀ c : ↥(qs_D mu nu), m c ∈ qs_ext nu K c.1) ∧ qs_ext mu y.1 = qs_rem (qs_D mu nu) (qs_ext nu K) m then
          (if ∀ x, qs_cnt m x = (y.2.1 x : ℕ) then
            ∏ c : ↥(qs_D mu nu), qs_sg ((qs_ext nu K c.1).erase (m c)) (m c) else 0) else 0 : ℤ)) : GLCoord ℤ n) =
      ∑ a : ↥(qs_D mu nu) → Fin n, if (∀ x, qs_cnt a x = (α.1 x : ℕ)) then
        ((detU n ^ mu (lastIdx n) : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) *
          (if ∀ c : ↥(qs_D mu nu), m c ∈ qs_ext nu K c.1 then
            (∏ c : ↥(qs_D mu nu), ((qs_sg ((qs_ext nu K c.1).erase (m c)) (m c) : ℤ) : GLCoord ℤ n)) *
              (∏ c ∈ Finset.Ioc (mu (lastIdx n)) (nu 0), qs_mn (qs_gC n) (qs_ext mu J c) (qs_rem (qs_D mu nu) (qs_ext nu K) m c)) *
              ∏ c : ↥(qs_D mu nu), qs_gC n (a c) (m c) else 0) else 0 := by
    intro m
    rw [Fintype.sum_prod_type]
    obtain ⟨f, hf⟩ : ∃ f : (ℤ → Finset (Fin n)) → GLCoord ℤ n, f =
        fun E => qs_TM (mu (lastIdx n)) (Finset.Ioc (mu (lastIdx n)) (nu 0)) (qs_ext mu J) E *
          ∑ β : SymIdx n b, qs_SM (qs_gC n) b α β *
            (if ∀ x, qs_cnt m x = (β.1 x : ℕ) then
              (∏ c : ↥(qs_D mu nu), ((qs_sg ((qs_ext nu K c.1).erase (m c)) (m c) : ℤ) : GLCoord ℤ n)) else 0) :=
      ⟨_, rfl⟩
    have h1 : ∀ I : TIdx mu, (∑ β : SymIdx n b, TMat mu J I * SymMat n b α β *
        (((if (∀ c : ↥(qs_D mu nu), m c ∈ qs_ext nu K c.1) ∧ qs_ext mu I = qs_rem (qs_D mu nu) (qs_ext nu K) m then
          (if ∀ x, qs_cnt m x = (β.1 x : ℕ) then
            ∏ c : ↥(qs_D mu nu), qs_sg ((qs_ext nu K c.1).erase (m c)) (m c) else 0) else 0 : ℤ)) : GLCoord ℤ n)) =
        if (∀ c : ↥(qs_D mu nu), m c ∈ qs_ext nu K c.1) ∧ qs_ext mu I = qs_rem (qs_D mu nu) (qs_ext nu K) m then
          f (qs_ext mu I)
        else 0 := by
      intro I
      rw [hf]
      split_ifs with h
      · simp only [hT, Finset.mul_sum, qs_SymMat_eq]
        refine Finset.sum_congr rfl fun β _ => ?_
        split_ifs
        · push_cast; ring
        · simp
      · simp
    rw [Finset.sum_congr rfl (fun I _ => h1 I),
      qs_collapse hmu _ _ (fun h => qs_rem_card hmu hnu hs _ (qs_ext_card hnu K) m h), hf]
    split_ifs with h
    · simp only [qs_sum_sym (qs_gC n) (qs_card_D hmu hnu hs) m α]
      rw [Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      split_ifs
      · rw [qs_TM]; ring
      · simp
    · simp
  have h2 : ∀ y : TIdx mu × SymIdx n b, TMat mu J y.1 * SymMat n b α y.2 * ((qs_ps b mu nu y K : ℤ) : GLCoord ℤ n) =
      ∑ m : ↥(qs_D mu nu) → Fin n, TMat mu J y.1 * SymMat n b α y.2 *
        (((if (∀ c : ↥(qs_D mu nu), m c ∈ qs_ext nu K c.1) ∧ qs_ext mu y.1 = qs_rem (qs_D mu nu) (qs_ext nu K) m then
          (if ∀ x, qs_cnt m x = (y.2.1 x : ℕ) then
            ∏ c : ↥(qs_D mu nu), qs_sg ((qs_ext nu K c.1).erase (m c)) (m c) else 0) else 0 : ℤ)) : GLCoord ℤ n) := by
    intro y
    rw [qs_ps, Int.cast_sum, Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun y _ => h2 y), Finset.sum_comm, Finset.sum_congr rfl (fun m _ => hm m),
    Finset.sum_comm, qs_mid]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : ∀ x, qs_cnt a x = (α.1 x : ℕ)
  · simp only [if_pos h]
    rw [← Finset.mul_sum, qs_core (qs_gC n) _ _ (qs_D_sub mu nu)]
  · simp only [if_neg h, Finset.sum_const_zero]

open Classical in
theorem qs_ps_right (b : ℕ) {mu nu : Fin n → ℤ} (hmu : Dominant mu) (hnu : Dominant nu) (hs : HStrip mu nu b)
    (J : TIdx mu) (α : SymIdx n b) (K : TIdx nu) :
    ∑ K' : TIdx nu, ((qs_ps b mu nu (J, α) K' : ℤ) : GLCoord ℤ n) * TMat nu K' K = qs_mid b mu nu J α K := by
  have hT : ∀ K', TMat nu K' K = qs_TM (mu (lastIdx n)) (Finset.Ioc (mu (lastIdx n)) (nu 0)) (qs_ext nu K') (qs_ext nu K) :=
    fun K' => qs_TMat_eq hnu _ _ (hs.1 _) le_rfl K' K
  obtain ⟨f, hf⟩ : ∃ f : (↥(qs_D mu nu) → Fin n) → (ℤ → Finset (Fin n)) → GLCoord ℤ n, f =
      fun a E => (if ∀ x, qs_cnt a x = (α.1 x : ℕ) then
            (∏ c : ↥(qs_D mu nu), ((qs_sg ((E c.1).erase (a c)) (a c) : ℤ) : GLCoord ℤ n)) *
              qs_TM (mu (lastIdx n)) (Finset.Ioc (mu (lastIdx n)) (nu 0)) E (qs_ext nu K) else 0) := ⟨_, rfl⟩
  have h2 : ∀ K' : TIdx nu, ((qs_ps b mu nu (J, α) K' : ℤ) : GLCoord ℤ n) * TMat nu K' K =
      ∑ a : ↥(qs_D mu nu) → Fin n,
        if (∀ c : ↥(qs_D mu nu), a c ∉ qs_ext mu J c.1) ∧ qs_ext nu K' = qs_add (qs_D mu nu) (qs_ext mu J) a then
          f a (qs_ext nu K')
        else 0 := by
    intro K'
    rw [qs_ps, Int.cast_sum, Finset.sum_mul, hf]
    refine Finset.sum_congr rfl fun a _ => ?_
    have := qs_rem_iff_add (qs_D mu nu) (qs_ext mu J) (qs_ext nu K') a
    by_cases h : (∀ c : ↥(qs_D mu nu), a c ∈ qs_ext nu K' c.1) ∧ qs_ext mu J = qs_rem (qs_D mu nu) (qs_ext nu K') a
    · rw [if_pos h, if_pos (this.1 h)]
      simp only [hT]
      split_ifs
      · push_cast; ring
      · simp
    · rw [if_neg h, if_neg (fun h' => h (this.2 h'))]; simp
  rw [Finset.sum_congr rfl (fun K' _ => h2 K'), Finset.sum_comm, qs_mid]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [qs_collapse hnu _ _ (fun h => qs_add_card hmu hnu hs _ (qs_ext_card hmu J) a h), hf]
  by_cases h : ∀ c : ↥(qs_D mu nu), a c ∉ qs_ext mu J c.1
  · rw [if_pos h, if_pos h]
    have h3 : ∀ c : ↥(qs_D mu nu), (qs_add (qs_D mu nu) (qs_ext mu J) a c.1).erase (a c) = qs_ext mu J c.1 := by
      intro c; rw [qs_add_mem, Finset.erase_insert (h c)]
    simp only [h3]
    split_ifs
    · rw [qs_TM]; ring
    · rfl
  · rw [if_neg h, if_neg h]; simp

theorem qs_ps_lead (b : ℕ) {mu nu : Fin n → ℤ} (hmu : Dominant mu) (hnu : Dominant nu) (hs : HStrip mu nu b) :
    qs_ps b mu nu (canT mu, qs_mon (qs_card_D hmu hnu hs) (qs_mc mu nu)) (canT nu) = 1 := by
  rw [qs_ps, Finset.sum_eq_single (qs_mc mu nu)]
  · rw [if_pos ((qs_can_iff hmu hnu hs _).2 rfl), if_pos]
    swap
    · intro x; rfl
    refine Finset.prod_eq_one fun c _ => ?_
    rw [qs_ext_can hnu, (qs_mem_D hmu hnu c.1).1 c.2]
    have hlt : colH mu c.1 < n := (qs_mc mu nu c).2
    show qs_sg ((qs_ini (colH mu c.1 + 1)).erase ⟨colH mu c.1, hlt⟩) ⟨colH mu c.1, hlt⟩ = 1
    rw [qs_ini_erase, qs_sg_ini]
  · intro m _ hm
    rw [if_neg (fun h => hm ((qs_can_iff hmu hnu hs _).1 h))]
  · intro h; exact absurd (Finset.mem_univ _) h

omit [NeZero n] in
lemma qs_gC_torus : (qs_gC n).map (evGL (torusPt n)) =
    Matrix.diagonal fun a => AddMonoidAlgebra.single (Pi.single a (1 : ℤ)) (1 : ℤ) := by
  ext a b
  simp only [Matrix.map_apply, qs_gC, Matrix.of_apply, qb_evGL_algebraMap, genMat, MvPolynomial.coe_eval₂Hom,
    MvPolynomial.eval₂_X]
  rfl

omit [NeZero n] in
lemma qs_prod_torus (ε : ℤ) (f : Fin n → ℕ) :
    ∏ x, (AddMonoidAlgebra.single (Pi.single x ε : Fin n → ℤ) (1 : ℤ)) ^ (f x) =
      AddMonoidAlgebra.single (fun x => ε * (f x : ℤ)) 1 := by
  simp_rw [AddMonoidAlgebra.single_pow, one_pow]
  rw [qb_prod_single]
  congr 1
  funext y
  simp [Finset.sum_apply, Pi.single_apply, mul_comm]

omit [NeZero n] in
open Classical in
lemma qs_mem_strUp {mu nu : Fin n → ℤ} {b : ℕ} (h : nu ∈ strUp mu b) : HStrip mu nu b := (Finset.mem_filter.1 h).2

theorem symStrip_of : CntSym → SymStrip := by
  intro hc n _ b
  refine ⟨fun α x => ((α.1 x : ℕ) : ℤ), qs_ps b, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro α β h
    exact Subtype.ext (funext fun x => Fin.ext (by have := congrFun h x; simp only at this; exact_mod_cast this))
  · intro k l
    rw [qs_SymMat_eq, qs_SM_map, qs_gC_torus, qs_SM_diag]
    split_ifs with h
    · subst h
      rw [qs_prod_torus]; simp
    · rfl
  · intro mu hmu nu hnu
    exact qs_dom_up hmu (qs_mem_strUp hnu)
  · intro mu hmu nu hnu
    have hs := qs_mem_strUp hnu
    have hnu' := qs_dom_up hmu hs
    ext ⟨J, α⟩ K
    exact (qs_ps_left b hmu hnu' hs J α K).trans (qs_ps_right b hmu hnu' hs J α K).symm
  · intro mu hmu nu hnu
    have hs := qs_mem_strUp hnu
    have hnu' := qs_dom_up hmu hs
    refine ⟨qs_mon (qs_card_D hmu hnu' hs) (qs_mc mu nu), ?_, Or.inl (qs_ps_lead b hmu hnu' hs)⟩
    funext x
    exact qs_cnt_mc hmu hnu' hs x
  · intro mu hmu
    exact hc n mu b hmu

end Formalism.InvariantFactorPaths.ColumnFamilies
